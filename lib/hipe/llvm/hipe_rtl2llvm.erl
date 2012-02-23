%% -*- erlang-indent-level: 2 -*-

%%TODO:
%% -- Inline ASM stack adjustment
%% -- Const Labels

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").

-export([translate/2,
         fix_mfa_name/1]).

-include("../rtl/hipe_rtl.hrl").
-include("../rtl/hipe_literals.hrl").
-include("hipe_llvm.hrl").
-include("hipe_llvm_arch.hrl").
-include("llevm.hrl").

%-define(LLVM_DEBUG, true).
-ifdef(LLVM_DEBUG).
-define(debug_msg(Msg,Data), io:format(Msg,Data)).
-define(debug_rtl(Code, FunName), print_rtl(Code, FunName)).
-else.
-define(debug_msg(Msg,Data), no__debug).
-define(debug_rtl(Code, FunName), ok).
-endif.

-define(WORD_TYPE, llevm:'LLVMInt64Type'()).
-define(WORD_TYPE_P, llevm:'LLVMPointerType'(?WORD_TYPE, 0)).
-define(FLOAT_TYPE, llevm:'LLVMDoubleType'()).
-define(FLOAT_TYPE_P, llevm:'LLVMPointerType'(?FLOAT_TYPE, 0)).
-define(BYTE_TYPE, llevm:'LLVMInt8Type'()).
-define(BYTE_TYPE_P, llevm:'LLVMPointerType'(?BYTE_TYPE, 0)).
-define(FUN_RETURN_TYPE, createTypeFunRet()).


%%------------------------------------------------------------------------------
%% @doc Main function for translating an RTL function to LLVM Assembly. Takes as
%% input the RTL code and the variable indexes of possible garbage collection
%% roots and returns the corresponing LLVM, a dictionary with all the
%% relocations in the code and a hipe_constab() with informaton about data
%%------------------------------------------------------------------------------
translate(RTL, Roots) ->
  Fun = hipe_rtl:rtl_fun(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  Data = hipe_rtl:rtl_data(RTL),
  Code = hipe_rtl:rtl_code(RTL),
  %% Append Precoloured registers to Calls params and return values
  {Code1, Params1} = pin_precoloured_regs(Code, Params),
  {ModName, FunName_, _Arity} = fix_mfa_name(Fun),
  ?debug_rtl(RTL, FunName_),
  %% Init unique symbol generator and initialize the label counter to the last
  %% RTL label.
  hipe_gensym:init(llvm),
  {_, MaxLabel} = hipe_rtl:rtl_label_range(RTL),
  put({llvm,label_count}, MaxLabel+1),
  %% Initialize the relocation and symbol tables
  Relocs = relocs_init(),
  SymTab = symtab_init(),
 
  Ctx = llevm:'LLVMGetGlobalContext'(),
  %% Create Module
  Module = llevm:'LLVMModuleCreateWithName'(ModName),
  SymTab1 = symtab_insert(modRef, Module, SymTab),
  %% Create Function Definition
  ParamsNr = length(Params1),
  FunType = llevm:'LLVMFunctionType'(?FUN_RETURN_TYPE, fun_args_type(ParamsNr),
                                     ParamsNr, false),
  FunName = mkMFAName(Fun),
  Function = llevm:'LLVMAddFunction'(Module, FunName, FunType),
  llevm:'LLVMSetFunctionCallConv'(Function, 11),
  llevm:'LLVMAddFunctionAttr'(Function, ?LLVMNoRedZoneAttribute),
  llevm:'LLVMAddFunctionAttr'(Function, ?LLVMNoUnwindAttribute),
  llevm:'LLVMSetGC'(Function, "erlang_gc"),
  SymTab2 = symtab_insert(funRef, Function, SymTab1),
  %XXX:
  SymTab22 = symtab_insert({call, FunName}, Function, SymTab2),
  %% Create Builder 
  Builder = llevm:'LLVMCreateBuilderInContext'(Ctx),
  %% Create Entry Block
  EntryBB = llevm:'LLVMAppendBasicBlock'(Function, "Entry"),
  llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBB),
  %% Store current block
  SymTab3 = symtab_insert(bbRef, EntryBB, SymTab22),
  %% Store function arguments to correspongin stack slots
  SymTab4 = store_args(Params1, Function, Builder, SymTab3),
  %% Mark GC Roots
  SymTab5 = declare_roots(Roots, Builder, SymTab4),
  %% Translate RTL code
  {SymTab6, Relocs1, Data1} =
    translate_instr_list(Code1, Builder, SymTab5, Relocs, Data),
  %% Jump from Entry block to the first block of the RTL code
  FirstLabel = find_first_label(Code1),
  {FirstBB, SymTab7} = load_label(FirstLabel, SymTab6),
  llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBB),
  llevm:'LLVMBuildBr'(Builder, FirstBB),
  %% Hard-coded store of inc_stack function (which is added to prologue by LLVM)
  Relocs2 = relocs_store("inc_stack_0", {call, {bif, inc_stack_0, 0}}, Relocs1),
  %% Hard-coded store of llvm_fix_pinned_regs function
  Relocs3 = relocs_store("hipe_bifs.llvm_fix_pinned_regs.0",{call,
                         {hipe_bifs,llvm_fix_pinned_regs,0}}, Relocs2),
  {Relocs4, _SymTab8} = declare_closures(Relocs3, SymTab7),
  %% Dump only for debug
  %% llevm:'LLVMWriteBitcodeToFile'(Module, "foo.bc"),
  %% llevm:'LLVMDumpModule'(Module),
  {Module, Relocs4, Data1}.

%% Create the return type of the function
createTypeFunRet() ->
  RetNr = ?NR_PINNED_REGS+1,
  RetList = lists:duplicate(RetNr, ?WORD_TYPE),
  RetType = list_to_tuple(RetList),
  llevm:'LLVMStructType'(RetType, RetNr, false).

%% Create the type of the function arguments
fun_args_type(ArgsNr) ->
  ArgsType = lists:duplicate(ArgsNr, ?WORD_TYPE),
  list_to_tuple(ArgsType).

%% Store function parameters to corresponding variables
store_args(Params, Function, Builder, SymTab) ->
  %% Revese stack arguments in order to match with HiPE CC
  Params1 = reverse_stack_args(Params),
  store_args(Params1, Function, Builder, SymTab, 0).

store_args([], _Function, _Builder, SymTab, _N) -> SymTab;
store_args([P|Ps], Function, Builder, SymTab, N) ->
  ParamRef = llevm:'LLVMGetParam'(Function, N),
  SymTab1 = store_opnd(ParamRef, P, Builder, SymTab),
  store_args(Ps, Function, Builder, SymTab1, N+1).

%% Declare GC Roots, by calling llvm.gcroot function
declare_roots([], _Builder, SymTab) ->
  SymTab;
declare_roots(Roots, Builder, SymTab) ->
  Module = symtab_fetch_mod(SymTab),
  %% Create Metadata reference
  Metadata = llevm:'LLVMAddGlobal'(Module, ?BYTE_TYPE, "gc_metadata"),
  llevm:'LLVMSetGlobalConstant'(Metadata, true),
  %% Create llvm.gcroot function reference
  RetType = llevm:'LLVMVoidType'(),
  ArgsType = {llevm:'LLVMPointerType'(?BYTE_TYPE_P, 0), ?BYTE_TYPE_P},
  FunType = llevm:'LLVMFunctionType'(RetType, ArgsType, 2, false),
  GCRootFunction = llevm:'LLVMAddFunction'(Module, "llvm.gcroot", FunType),
  do_declare_roots(Roots, Builder, SymTab, GCRootFunction, Metadata).

do_declare_roots([], _, SymTab, _, _) -> SymTab;
do_declare_roots([R|Rs], Builder, SymTab, GCRootFunction, Metadata) ->
  %XXX: Fix this
  ByteTypePP = llevm:'LLVMPointerType'(?BYTE_TYPE_P, 0),
  {AllocaPtr, SymTab1} =
    case symtab_fetch({var, R}, SymTab) of
      undefined ->
        VarName = mkVarName(R),
        Value = llevm:'LLVMBuildAlloca'(Builder, ?WORD_TYPE, VarName),
        SymTab2 = symtab_insert({var, R}, Value, SymTab),
        {Value, SymTab2};
      Value ->
        {Value, SymTab}
    end,
  Ptr = llevm:'LLVMBuildBitCast'(Builder, AllocaPtr, ByteTypePP, ""),
  llevm:'LLVMBuildCall'(Builder, GCRootFunction, {Ptr, Metadata}, 2, ""),
  do_declare_roots(Rs, Builder, SymTab1, GCRootFunction, Metadata).

%%
translate_instr_list([], _Builder, SymTab,  Relocs, Data) ->
  {SymTab, Relocs, Data};
translate_instr_list([I|Is], Builder, SymTab, Relocs, Data) ->
  {SymTab1, Relocs1, Data1} = translate_instr(I, Builder, SymTab, Relocs, Data),
  translate_instr_list(Is, Builder, SymTab1, Relocs1, Data1).

translate_instr(I, Builder, SymTab, Relocs, Data) ->
  ?debug_msg("Translating ~w~n", [I]),
  case I of
    #alu{} ->
      SymTab1 = trans_alu(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #alub{} ->
      SymTab1 = trans_alub(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #branch{} ->
      SymTab1 = trans_branch(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #call{} ->
      {SymTab1, Relocs1} = case hipe_rtl:call_fun(I) of
        %% In AMD64 this instruction does nothing!
        %% TODO: chech use of fwait in other architectures!
        fwait ->
          {SymTab, Relocs};
        _ ->
          trans_call(I, Builder, SymTab, Relocs)
      end,
      {SymTab1, Relocs1, Data};
    #comment{} ->
      {SymTab, Relocs, Data};
    #enter{} ->
      {SymTab1, Relocs1} = trans_enter(I, Builder, SymTab, Relocs),
      {SymTab1, Relocs1, Data};
    #goto{} ->
      SymTab1 = trans_goto(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #label{} ->
      SymTab1 = trans_label(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #load{} ->
      SymTab1 = trans_load(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #load_address{} ->
      {SymTab1, Relocs1} = trans_load_address(I, Builder, SymTab, Relocs),
      {SymTab1, Relocs1, Data};
    #load_atom{} ->
      {SymTab1, Relocs1} = trans_load_atom(I, Builder, SymTab, Relocs),
      {SymTab1, Relocs1, Data};
    #move{} ->
      SymTab1 = trans_move(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #return{} ->
      trans_return(I, Builder, SymTab),
      {SymTab, Relocs, Data};
    #store{} ->
      SymTab1 = trans_store(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #fconv{} ->
      SymTab1 = trans_fconv(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #fload{} ->
      SymTab1 = trans_fload(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #fmove{} ->
      SymTab1 = trans_fmove(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #fp{} ->
      SymTab1 = trans_fp(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #fp_unop{} ->
      SymTab1 = trans_fp_unop(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #fstore{} ->
      SymTab1 = trans_fstore(I, Builder, SymTab),
      {SymTab1, Relocs, Data};
    #switch{} -> %% Only switch instruction updates Data
      trans_switch(I, Builder, SymTab, Relocs, Data);
    Other ->
       exit({?MODULE, translate_instr, {"unknown RTL instruction", Other}})
  end.

%%
%% alu
%%
trans_alu(I, Builder, SymTab) ->
  RtlDst = hipe_rtl:alu_dst(I),
  {Src1, SymTab1} = load_opnd(hipe_rtl:alu_src1(I), Builder, SymTab),
  {Src2, SymTab2} = load_opnd(hipe_rtl:alu_src2(I), Builder, SymTab1),
  Value =
    case hipe_rtl:alu_op(I) of
      'add' -> llevm:'LLVMBuildAdd'(Builder, Src1, Src2, "");
      'sub' -> llevm:'LLVMBuildSub'(Builder, Src1, Src2, "");
      'or'  -> llevm:'LLVMBuildOr'(Builder, Src1, Src2, "");
      'and' -> llevm:'LLVMBuildAnd'(Builder, Src1, Src2, "");
      'xor' -> llevm:'LLVMBuildXor'(Builder, Src1, Src2, "");
      'sll' -> llevm:'LLVMBuildShl'(Builder, Src1, Src2, "");
      'srl' -> llevm:'LLVMBuildLShr'(Builder, Src1, Src2, "");
      'sra' -> llevm:'LLVMBuildAShr'(Builder, Src1, Src2, "");
      'mul' -> llevm:'LLVMBuildMul'(Builder, Src1, Src2, "");
      'fdiv' -> llevm:'LLVMBuildFDiv'(Builder, Src1, Src2, "");
      'sdiv' -> llevm:'LLVMBuildSDiv'(Builder, Src1, Src2, "");
      'srem' -> llevm:'LLVMBuildSDem'(Builder, Src1, Src2, "");
       Other -> exit({?MODULE, trans_alu, {"Unknown RTL Operator", Other}})
     end,
  store_opnd(Value, RtlDst, Builder, SymTab2).

%%
%% alub
%%
trans_alub(I, Builder, SymTab) ->
  case hipe_rtl:alub_cond(I) of
    Op  when Op=:= overflow orelse Op =:= not_overflow ->
      trans_alub_overflow(I, Builder, SymTab, signed);
    ltu -> %% ltu means unsigned overflow
      trans_alub_overflow(I, Builder, SymTab, unsigned);
    _ ->
      trans_alub_no_overflow(I, Builder, SymTab)
  end.

trans_alub_overflow(I, Builder, SymTab, Sign) ->
  {Src1, SymTab1} = load_opnd(hipe_rtl:alub_src1(I), Builder, SymTab),
  {Src2, SymTab2} = load_opnd(hipe_rtl:alub_src2(I), Builder, SymTab1),
  RtlDst = hipe_rtl:alub_dst(I),
  %% Create operation with overflow check
  Name = trans_alub_op(I, Sign),
  RetType = llevm:'LLVMStructType'({?WORD_TYPE, llevm:'LLVMInt1Type'()}, 2,
                                   false),
  ArgsType = {?WORD_TYPE, ?WORD_TYPE},
  {Function, SymTab3} = load_call(Name, RetType, ArgsType, 2, [], SymTab2),
  RetStruct = llevm:'LLVMBuildCall'(Builder, Function, {Src1, Src2}, 2, ""),
  %% Extract the result and store it
  Result = llevm:'LLVMBuildExtractValue'(Builder, RetStruct, 0, ""),
  SymTab4 = store_opnd(Result, RtlDst, Builder, SymTab3),
  %% Check if an overflow happened and jump to corresponding block
  Overflow = llevm:'LLVMBuildExtractValue'(Builder, RetStruct, 1, ""),
  case hipe_rtl:alub_cond(I) of
    Op when Op =:= overflow orelse Op =:= ltu ->
      {TrueBB, SymTab5} = load_label(hipe_rtl:alub_true_label(I),SymTab4),
      {FalseBB, SymTab6} = load_label(hipe_rtl:alub_false_label(I), SymTab5);
    not_overflow ->
      {TrueBB, SymTab5} = load_label(hipe_rtl:alub_false_label(I), SymTab4),
      {FalseBB, SymTab6} = load_label(hipe_rtl:alub_true_label(I), SymTab5)
  end,
  llevm:'LLVMBuildCondBr'(Builder, Overflow, TrueBB, FalseBB),
  SymTab6.

trans_alub_no_overflow(I, Builder, SymTab) ->
  %% alu
  AluI = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
                         hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  SymTab1 = trans_alu(AluI, Builder, SymTab),
  %% icmp
  {Dst, SymTab2} = load_opnd(hipe_rtl:alub_dst(I), Builder, SymTab1),
  Cond = trans_rel_op(hipe_rtl:alub_cond(I)),
  ZeroConst = llevm:'LLVMConstInt'(?WORD_TYPE, 0, true),
  IfRef = llevm:'LLVMBuildICmp'(Builder, Cond, Dst, ZeroConst, ""),
  %% br
  {TrueBB, SymTab3} = load_label(hipe_rtl:alub_true_label(I), SymTab2),
  {FalseBB, SymTab4} = load_label(hipe_rtl:alub_false_label(I), SymTab3),
  llevm:'LLVMBuildCondBr'(Builder, IfRef, TrueBB, FalseBB),
  SymTab4.

%%
%% branch
%%
trans_branch(I, Builder, SymTab) ->
  {Src1, SymTab1} = load_opnd(hipe_rtl:branch_src1(I), Builder, SymTab),
  {Src2, SymTab2} = load_opnd(hipe_rtl:branch_src2(I), Builder, SymTab1),
  Cond = trans_rel_op(hipe_rtl:branch_cond(I)),
  %% icmp
  If = llevm:'LLVMBuildICmp'(Builder, Cond, Src1, Src2, ""),
  %% br
  {TrueBB, SymTab3} = load_label(hipe_rtl:branch_true_label(I), SymTab2),
  {FalseBB, SymTab4} = load_label(hipe_rtl:branch_false_label(I), SymTab3),
  llevm:'LLVMBuildCondBr'(Builder, If, TrueBB, FalseBB),
  SymTab4.

%%
%% call
%%
trans_call(I, Builder, SymTab, Relocs) ->
  %% Reverse stack arguments in order to match HiPE CC
  ArgList= reverse_stack_args(hipe_rtl:call_arglist(I)),
  RetList = hipe_rtl:call_dstlist(I),
  CallName = hipe_rtl:call_fun(I),
  %% Expose the closure, if needed
  {SymTab1, Relocs1} = expose_closure(Builder, SymTab, CallName, ArgList,
                                      Relocs),
  %% XXX: Is this Correct ?
  %% Loading the arguments cannot change the SymTab, so we ignore it
  {ArgListRef, _} = lists:unzip([ load_opnd(X, Builder, SymTab1) || X<-ArgList ]),
  {Function, SymTab2, Relocs2} =  trans_call_name(Builder, SymTab1, Relocs1,
                                                  CallName, ArgList, RetList),
  FinalSymTab = case hipe_rtl:call_fail(I) of
    [] -> %% Call Without Exception Handler
      RetStruct = llevm:'LLVMBuildCall'(Builder, Function,
                                        list_to_tuple(ArgListRef),
                                        length(ArgListRef), ""),
      llevm:'LLVMSetInstructionCallConv'(RetStruct, 11),
      SymTab3 = store_call_retlist(RetStruct, RetList, Builder, SymTab2),
      case  hipe_rtl:call_continuation(I) of
        [] ->
          SymTab3;
        ContLabel -> %% Call with normal continuation
          {ContBB, SymTab4} = load_label(ContLabel, SymTab3),
          llevm:'LLVMBuildBr'(Builder, ContBB),
          SymTab4
      end;
    FailLabel -> %% Call With Exception Handler
      ContLabel = hipe_rtl:call_continuation(I),
      NewContLabel = hipe_gensym:new_label(llvm),
      NewFailLabel = hipe_gensym:new_label(llvm),
      {ContBB, SymTab3} = load_label(NewContLabel, SymTab2),
      {FailBB, SymTab4} = load_label(NewFailLabel, SymTab3),
      RetStruct = llevm:'LLVMBuildInvoke'(Builder, Function,
                                          list_to_tuple(ArgListRef),
                                          length(ArgListRef), ContBB, FailBB,
                                          ""),
      llevm:'LLVMSetInstructionCallConv'(RetStruct, 11),
      %% Create the code for the new fail block
      SymTab5 = create_new_fail_block(NewFailLabel, FailLabel, ArgList, RetList,
                                      Builder, SymTab4),
      %% Create the code for the new continuation block
      SymTab6 = create_new_cont_block(NewContLabel, ContLabel, RetStruct,
                                      RetList, Builder, SymTab5),
      %% XXX: Restore Builder at current position ? Not needed because calls
      %% with exception handlers are always block terminating instructions
      SymTab6
  end,
  {FinalSymTab, Relocs2}.

store_call_retlist(RetStruct, RetList, Builder, SymTab) ->
  store_call_retlist(RetStruct, RetList, Builder, SymTab, 0).

store_call_retlist(_RetStruct, [], _Builder, SymTab, _Num) ->
  SymTab;
store_call_retlist(RetStruct, [none | Rs], Builder, SymTab, Num) ->
  store_call_retlist(RetStruct, Rs, Builder, SymTab, Num+1);
store_call_retlist(RetStruct, [R|Rs], Builder, SymTab, Num) ->
  Value = llevm:'LLVMBuildExtractValue'(Builder, RetStruct, Num, ""),
  SymTab1 = store_opnd(Value, R, Builder, SymTab),
  store_call_retlist(RetStruct, Rs, Builder, SymTab1, Num+1).

create_new_fail_block(NewFailLabel, FailLabel, ArgList, RetList, Builder, SymTab) ->
  SymTab1 = trans_label(hipe_rtl:mk_label(NewFailLabel), Builder, SymTab),
  %% Personality Function And Landing Pad
  {PersFunction, SymTab2} = create_personality_function(SymTab1),
  LandPad= llevm:'LLVMBuildLandingPad'(Builder, llevm:'LLVMInt32Type'(),
                                       PersFunction, 0, ""),
  llevm:'LLVMSetCleanup'(LandPad, true),
  %% Stack Pointer Adjustment
  SpAdj = find_sp_adj(ArgList),
  case SpAdj>0 of
    true ->
      AsmFunType = llevm:'LLVMFunctionType'(llevm:'LLVMVoidType'(),
                                            {?WORD_TYPE}, 1, false),
      StackPointer = ?ARCH_REGISTERS:reg_name(?ARCH_REGISTERS:sp()),
      AsmString = "sub $0, " ++ StackPointer,
      AsmFun = llevm:'LLVMConstInlineAsm'(AsmFunType, AsmString, "r",
                                 true, false),
      ConstSpAdj = llevm:'LLVMConstInt'(?WORD_TYPE, 1, false),
      llevm:'LLVMBuildCall'(Builder, AsmFun, {ConstSpAdj}, 1, "");
    false -> ok
  end,
  %% hipe_bifs:llvm_fix_pinned_regs()
  {BifRetList, _} = lists:split(?NR_PINNED_REGS, RetList),
  {BifFunction, SymTab3} = create_bif_pinned_regs(SymTab2, BifRetList),
  RetStruct = llevm:'LLVMBuildCall'(Builder, BifFunction, {}, 0, ""),
  llevm:'LLVMSetInstructionCallConv'(RetStruct, 11),
  SymTab4 = store_call_retlist(RetStruct, BifRetList, Builder, SymTab3),
  trans_goto(hipe_rtl:mk_goto(FailLabel), Builder, SymTab4).

find_sp_adj(ArgList) ->
  NrArgs = length(ArgList),
  RegArgs = ?NR_ARG_REGS+?NR_PINNED_REGS,
  case NrArgs > RegArgs of
    true ->
      (NrArgs-RegArgs)*(?WORD_WIDTH div 8);
    false ->
      0
  end.

create_personality_function(SymTab) ->
  PersFnName = "__gcc_personality_v0",
  RetType = llevm:'LLVMInt32Type'(),
  ArgsType = {
    llevm:'LLVMInt32Type'(),
    llevm:'LLVMInt64Type'(),
    llevm:'LLVMPointerType'(llevm:'LLVMInt8Type'(), 0),
    llevm:'LLVMPointerType'(llevm:'LLVMInt8Type'(), 0)},
  load_call(PersFnName, RetType, ArgsType, 4, [], SymTab).

create_bif_pinned_regs(SymTab, RetList) ->
  BifName = "hipe_bifs.llvm_fix_pinned_regs.0",
  RetTypeList = ([?WORD_TYPE || _ <- RetList]),
  RetType = llevm:'LLVMStructType'(list_to_tuple(RetTypeList),
                                  length(RetTypeList), false),
  ArgsType = {},
  load_call(BifName, RetType, ArgsType, 0, cc11, SymTab).

create_new_cont_block(NewContLabel, ContLabel, RetStruct, RetList, Builder, SymTab) ->
  SymTab2 = trans_label(hipe_rtl:mk_label(NewContLabel), Builder, SymTab),
  SymTab3 = store_call_retlist(RetStruct, RetList, Builder, SymTab2),
  trans_goto(hipe_rtl:mk_goto(ContLabel), Builder, SymTab3).

%% In case of call to a register (closure call) with more than ?NR_ARG_REGS
%% arguments we must track the offset this call in the code, in order to
%% to correct the stack descriptor. So, we insert a new Label and add this label
%% to the "table_closures"
%% --------------------------------|--------------------------------------------
%%        Old Code                 |           New Code
%% --------------------------------|--------------------------------------------
%%                                 |           br %ClosureLabel
%%        call %reg(Args)          |           ClosureLabel:
%%                                 |           call %reg(Args)
expose_closure(Builder, SymTab, CallName, CallArgs, Relocs) ->
  case hipe_rtl:is_reg(CallName) andalso length(CallArgs) > ?NR_ARG_REGS+?NR_PINNED_REGS of
    true ->
      LabelNum = hipe_gensym:new_label(llvm),
      Label = hipe_rtl:mk_label(LabelNum),
      {BBRef, SymTab1} = load_label(LabelNum, SymTab),
      llevm:'LLVMBuildBr'(Builder, BBRef),
      SymTab2 = trans_label(Label, Builder, SymTab1),
      Relocs1 = relocs_store({CallName, Label}, {closure_label, LabelNum,
                              length(CallArgs) - ?NR_ARG_REGS - ?NR_PINNED_REGS},
                              Relocs),
      {SymTab2, Relocs1};
    false ->
      {SymTab, Relocs}
  end.

create_fun_decl(CallName, CallArgs, CallRet, SymTab) ->
  RetType = [ ?WORD_TYPE || _ <- CallRet ],
  RetType1 = llevm:'LLVMStructType'(list_to_tuple(RetType), length(RetType),
                                    false),
  ArgsType = [ ?WORD_TYPE || _ <- CallArgs ],
  load_call(CallName, RetType1, list_to_tuple(ArgsType), length(ArgsType), cc11,
            SymTab).

%%
trans_call_name(Builder, SymTab, Relocs,  CallName, CallArgs, CallRet) ->
  case CallName of
    PrimOp when is_atom(PrimOp) ->
      LLVMName = trans_prim_op(PrimOp),
      {Function, SymTab1} = create_fun_decl(LLVMName, CallArgs, CallRet, SymTab),
      Relocs1 = relocs_store(LLVMName, {call, {bif, PrimOp,
                             length(CallArgs)-?NR_PINNED_REGS}}, Relocs),
      {Function, SymTab1, Relocs1};
    {M, F, A} when is_atom(M), is_atom(F), is_integer(A) ->
      LLVMName = mkMFAName(fix_mfa_name({M,F,A})),
      {Function, SymTab1} = create_fun_decl(LLVMName, CallArgs, CallRet, SymTab),
      Relocs1 = relocs_store(LLVMName, {call, {M,F,A}}, Relocs),
      {Function, SymTab1, Relocs1};
    Reg ->
      case hipe_rtl:is_reg(Reg) of
        true -> %% In case of a closure call, the register holding the address
          %% of the closure must be converted to function type in
          %% order to make the call
          {RegRef, SymTab1} = load_opnd(Reg, Builder, SymTab),
          PtrRef =llevm:'LLVMBuildIntToPtr'(Builder, RegRef, ?WORD_TYPE_P, ""),
          RetType = [ ?WORD_TYPE || _ <- CallRet ],
          RetType1 = llevm:'LLVMStructType'(list_to_tuple(RetType), length(RetType),
                                            false),
          ArgsType = [ ?WORD_TYPE || _ <- CallArgs ],
          FunType = llevm:'LLVMFunctionType'(RetType1, list_to_tuple(ArgsType),
                                             length(ArgsType), false),
          FunTypePointer = llevm:'LLVMPointerType'(FunType, 0),
          Function = llevm:'LLVMBuildBitCast'(Builder, PtrRef, FunTypePointer, ""),
          llevm:'LLVMSetFunctionCallConv'(Function, 11),
          {Function, SymTab1, Relocs};
        false ->
          exit({?MODULE, trans_call_name, {"Unimplemted Call to", CallName}})
      end
  end.

%%%%
%%%% trans_comment
%%%%
%%trans_comment(I, Relocs) ->
%%  I1 = hipe_llvm:mk_comment(hipe_rtl:comment_text(I)),
%%  {I1, Relocs}.
%%

%%
%% enter
%%
trans_enter(I, Builder, SymTab, Relocs) ->
  %% Reverse stack arguments in order to match with hipe CC
  ArgList= reverse_stack_args(hipe_rtl:enter_arglist(I)),
  RetList = hipe_rtl:enter_dstlist(I),
  CallName = hipe_rtl:enter_fun(I),
  %% Loading the arguments cannot change the SymTab, so we ignore it
  %% XXX: Is This Correct ?
  {ArgListRef, _} = lists:unzip([ load_opnd(X, Builder, SymTab) || X<-ArgList ]),
  {Function, SymTab2, Relocs1} =  trans_call_name(Builder, SymTab, Relocs, CallName,
                                                  ArgList, RetList),
  RetStruct = llevm:'LLVMBuildCall'(Builder, Function, list_to_tuple(ArgListRef),
                                    length(ArgListRef), ""),
  llevm:'LLVMSetInstructionCallConv'(RetStruct, 11),
  llevm:'LLVMBuildRet'(Builder, RetStruct),
  {SymTab2, Relocs1}.

%%
%%
%% goto
%%
trans_goto(I, Builder, SymTab) ->
  Label = hipe_rtl:goto_label(I),
  {BBRef, SymTab1} = load_label(Label, SymTab),
  llevm:'LLVMBuildBr'(Builder, BBRef),
  SymTab1.

%%
%% label
%%
trans_label(I, Builder, SymTab) ->
  Label  = hipe_rtl:label_name(I),
  {BBRef, SymTab1} = load_label(Label, SymTab),
  %% Update the current block
  llevm:'LLVMPositionBuilderAtEnd'(Builder, BBRef),
  symtab_insert(bbRef, BBRef, SymTab1).

%%
%% load
%%
trans_load(I, Builder, SymTab) ->
  RtlDst = hipe_rtl:load_dst(I),
  {SrcRef, SymTab1} = load_opnd(hipe_rtl:load_src(I), Builder, SymTab),
  {OffsetRef, SymTab2} = load_opnd(hipe_rtl:load_offset(I), Builder,  SymTab1),
  ValueRef = llevm:'LLVMBuildAdd'(Builder, SrcRef, OffsetRef, ""),
  LoadedRef =
    case hipe_rtl:load_size(I) of
      word ->
        PtrRef = llevm:'LLVMBuildIntToPtr'(Builder, ValueRef, ?WORD_TYPE_P, ""),
        llevm:'LLVMBuildLoad'(Builder, PtrRef, "");
      Size ->
        LoadType = type_from_size(Size),
        LoadTypeP = llevm:'LLVMPointerType'(LoadType, 0),
        PtrRef = llevm:'LLVMBuildIntToPtr'(Builder, ValueRef, LoadTypeP, ""),
        LoadedRef_ = llevm:'LLVMBuildLoad'(Builder, PtrRef, ""),
        case hipe_rtl:load_sign(I) of
          signed -> llevm:'LLVMBuildSExt'(Builder, LoadedRef_, ?WORD_TYPE, "");
          unsigned -> llevm:'LLVMBuildZExt'(Builder, LoadedRef_, ?WORD_TYPE, "")
        end
    end,
  store_opnd(LoadedRef, RtlDst, Builder, SymTab2).

%%
%% load_address
%%
trans_load_address(I, Builder, SymTab, Relocs) ->
 RtlDst = hipe_rtl:load_address_dst(I),
 RtlAddr = hipe_rtl:load_address_addr(I),
 {AddrRef, SymTab2, Relocs2} =
    case hipe_rtl:load_address_type(I) of
      constant ->
        {ValueRef, SymTab1} = load_opnd(hipe_rtl:mk_const_label(RtlAddr), Builder, SymTab),
        Relocs1 = dict:store(mkConstLabelName(RtlAddr), {'constant', RtlAddr},
        Relocs),
        {ValueRef, SymTab1, Relocs1};
      closure  ->
        {Closure, _, _} = RtlAddr,
        {_, ClosureName, _} = fix_mfa_name(Closure),
        case symtab_fetch({closure, Closure}, SymTab) of
          undefined ->
            %% Declare a global constant and convert the pointer to integer
            Module = symtab_fetch(modRef, SymTab),
            FixedClosureName = atom_to_list(ClosureName),
            PtrRef = llevm:'LLVMAddGlobal'(Module, ?BYTE_TYPE, FixedClosureName),
            llevm:'LLVMSetGlobalConstant'(PtrRef, true),
            ValueRef = llevm:'LLVMBuildPtrToInt'(Builder, PtrRef, ?WORD_TYPE,
              ""),
            SymTab1 = symtab_insert({closure, Closure}, ValueRef, SymTab),
            Relocs1 = relocs_store(FixedClosureName, {closure, RtlAddr}, Relocs),
            {ValueRef, SymTab1, Relocs1};
          ValueRef ->
            {ValueRef, SymTab, Relocs}
        end;
      type ->
        exit({?MODULE, trans_load_address, {"Type not implemented in
              load_address", RtlAddr}})
    end,
  SymTab3 = store_opnd(AddrRef, RtlDst, Builder, SymTab2),
  {SymTab3, Relocs2}.


%%
%% load_atom
%%
trans_load_atom(I, Builder, SymTab, Relocs) ->
  Atom = hipe_rtl:load_atom_atom(I),
  {ValueRef , SymTab1} = trans_atom(Builder, Atom, SymTab),
  Dst = hipe_rtl:load_atom_dst(I),
  SymTab2 = store_opnd(ValueRef, Dst, Builder, SymTab1),
  AtomName = mkAtomName(Atom),
  Relocs1 = relocs_store(AtomName, {atom, Atom}, Relocs),
  {SymTab2, Relocs1}.


trans_atom(Builder, Atom, SymTab) ->
  case symtab_fetch({atom, Atom}, SymTab) of
    undefined ->
      %% Declare a global constant and convert the pointer to integer
      Module = symtab_fetch(modRef, SymTab),
      AtomName = mkAtomName(Atom),
      PtrRef = llevm:'LLVMAddGlobal'(Module, ?BYTE_TYPE, AtomName),
      llevm:'LLVMSetGlobalConstant'(PtrRef, true),
      ValueRef = llevm:'LLVMBuildPtrToInt'(Builder, PtrRef, ?WORD_TYPE, ""),
      SymTab1 = symtab_insert({atom, Atom}, ValueRef, SymTab),
      {ValueRef, SymTab1};
    ValueRef ->
      {ValueRef, SymTab}
  end.

%%
%% move
%%
trans_move(I, Builder, SymTab) ->
  RtlSrc = hipe_rtl:move_src(I),
  RtlDst = hipe_rtl:move_dst(I),
  {ValueRef, SymTab1} = load_opnd(RtlSrc, Builder, SymTab),
  store_opnd(ValueRef, RtlDst, Builder, SymTab1).


%%
%% return
%%
trans_return(I, Builder, SymTab) ->
  RetList = hipe_rtl:return_varlist(I),
  {RetListRef, _} = lists:unzip([load_opnd(X, Builder, SymTab) || X<-RetList]),
  RetListRef1 = list_to_tuple(RetListRef),
  llevm:'LLVMBuildAggregateRet'(Builder, RetListRef1, length(RetList)).

%%
%% store
%%
trans_store(I, Builder, SymTab) ->
  {BaseRef, SymTab1} = load_opnd(hipe_rtl:store_base(I), Builder, SymTab),
  {OffsetRef, SymTab2} = load_opnd(hipe_rtl:store_offset(I), Builder, SymTab1),
  {SrcRef, SymTab2} = load_opnd(hipe_rtl:store_src(I), Builder, SymTab2),
  ValueRef = llevm:'LLVMBuildAdd'(Builder, BaseRef, OffsetRef, "tempAdd"),
  case hipe_rtl:store_size(I) of
    word ->
      PtrRef = llevm:'LLVMBuildIntToPtr'(Builder, ValueRef, ?WORD_TYPE_P, "pointerTmp"),
      llevm:'LLVMBuildStore'(Builder, SrcRef, PtrRef);
    Size ->
      %% XXX: Is always trunc correct ?
      LoadType = type_from_size(Size),
      LoadTypePointer = llevm:'LLVMPointerType'(LoadType, 0),
      PtrRef = llevm:'LLVMBuildIntToPtr'(Builder, ValueRef, LoadTypePointer, "pointerTmp"),
      SrcRef2 = llevm:'LLVMBuildTrunc'(Builder, SrcRef, LoadType, "truncTmp"),
      llevm:'LLVMBuildStore'(Builder, SrcRef2, PtrRef)
  end,
  SymTab2.

%%
%% fconv
%%
trans_fconv(I, Builder, SymTab) ->
  RtlDst = hipe_rtl:fconv_dst(I),
  %%XXX: Can be a float cont label ? what about above conversion
  {ValueRef, SymTab1} = load_float(hipe_rtl:fconv_src(I), Builder, SymTab),
  ValueRef1 =  llevm:'LLVMBuildCast'(Builder, ?LLVMSIToFP, ValueRef,
                                     ?FLOAT_TYPE, ""),
  store_float(ValueRef1, RtlDst, Builder, SymTab1).

%% TODO: fload, fstore, fmove, and fp are almost the same with load,store,move
%% and alu. Maybe we should join them.
%%
%% fload
%%
trans_fload(I, Builder, SymTab) ->
  RtlDst = hipe_rtl:fload_dst(I),
  {SrcRef, SymTab1} = load_float(hipe_rtl:fload_src(I), Builder, SymTab),
  {OffsetRef, SymTab2} = load_float(hipe_rtl:fload_offset(I), Builder,  SymTab1),
  ValueRef = llevm:'LLVMBuildAdd'(Builder, SrcRef, OffsetRef, ""),
  PtrRef = llevm:'LLVMBuildIntToPtr'(Builder, ValueRef, ?FLOAT_TYPE_P, ""),
  LoadedRef =  llevm:'LLVMBuildLoad'(Builder, PtrRef, ""),
  store_float(LoadedRef, RtlDst, Builder, SymTab2).

%%
%% fmove
%%
trans_fmove(I, Builder, SymTab) ->
  RtlDst = hipe_rtl:fmove_dst(I),
  RtlSrc = hipe_rtl:fmove_src(I),
  {ValueRef, SymTab1} = load_float(RtlSrc, Builder, SymTab),
  store_float(ValueRef, RtlDst, Builder, SymTab1).

%%
%% fp
%%
trans_fp(I, Builder, SymTab) ->
  %% XXX: Just copied trans_alu...think again..
  RtlDst = hipe_rtl:fp_dst(I),
  {SrcRef1, SymTab1} = load_float(hipe_rtl:fp_src1(I), Builder, SymTab),
  {SrcRef2, SymTab2} = load_float(hipe_rtl:fp_src2(I), Builder, SymTab1),
  ValueRef =
    case hipe_rtl:fp_op(I) of
      'fadd' -> llevm:'LLVMBuildFAdd'(Builder, SrcRef1, SrcRef2, "");
      'fsub' -> llevm:'LLVMBuildFSub'(Builder, SrcRef1, SrcRef2, "");
      'fdiv' -> llevm:'LLVMBuildFDiv'(Builder, SrcRef1, SrcRef2, "");
      'fmul' -> llevm:'LLVMBuildMul'(Builder, SrcRef1, SrcRef2, "");
      'fchs' -> llevm:'LLVMBuildFSub'(Builder, SrcRef1, SrcRef2, "");
       Other -> exit({?MODULE, trans_alu, {"Unknown RTL Operator", Other}})
     end,
  SymTab3 = store_float(ValueRef, RtlDst, Builder, SymTab2),
  %% Synchronization point for floating point exceptions
  {PtrRef, SymTab5} = case symtab_fetch(float_sync_point, SymTab3) of
    undefined ->
      CurrentBBRef = symtab_fetch_bb(SymTab3),
      Function = symtab_fetch_fun(SymTab3),
      EntryBBRef = llevm:'LLVMGetEntryBasicBlock'(Function),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBBRef),
      PtrRef2 = llevm:'LLVMBuildAlloca'(Builder, ?FLOAT_TYPE,
                                       "float_sync_point"),
      SymTab4 = symtab_insert(float_sync, PtrRef2, SymTab3),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, CurrentBBRef),
      {PtrRef2, SymTab4};
    PtrRef2 -> {PtrRef2, SymTab3}
  end,
  llevm:'LLVMBuildVolatileStore'(Builder, ValueRef, PtrRef, true),
  llevm:'LLVMBuildVolatileLoad'(Builder, PtrRef, "", true),
  SymTab5.

%%
%% fp_unop
%%
trans_fp_unop(I, Builder, SymTab) ->
  io:format("FP UNOP~n"),
  RtlDst = hipe_rtl:fp_unop_dst(I),
  {SrcRef1, SymTab1} = load_float(hipe_rtl:fp_unop_src(I), Builder, SymTab),
  ZeroRef = llevm:'LLVMConstReal'(?FLOAT_TYPE, 0.0),
  ValueRef =
    case hipe_rtl:fp_unop_op(I) of
      'fadd' -> llevm:'LLVMBuildFAdd'(Builder, ZeroRef, SrcRef1, "");
      'fsub' -> llevm:'LLVMBuildFSub'(Builder, ZeroRef, SrcRef1, "");
      'fdiv' -> llevm:'LLVMBuildFDiv'(Builder, ZeroRef, SrcRef1, "");
      'fmul' -> llevm:'LLVMBuildMul'(Builder, ZeroRef, SrcRef1, "");
      'fchs' -> llevm:'LLVMBuildFSub'(Builder, ZeroRef, SrcRef1, "");
       Other -> exit({?MODULE, trans_fp_unop, {"Unknown RTL Operator", Other}})
     end,
  store_float(ValueRef, RtlDst, Builder, SymTab1).
%%%% TODO: Fix fp_unop in a way like the following. You must change trans_dest,
%%%% in order to call float_to_list in a case of float constant. Maybe the type
%%%% check is expensive...
%%%% Dst = hipe_rtl:fp_unop_dst(I),
%%%% Src = hipe_rtl:fp_unop_src(I),
%%%% Op = hipe_rtl:fp_unop_op(I),
%%%% Zero = hipe_rtl:mk_imm(0.0),
%%%% I1 = hipe_rtl:mk_fp(Dst, Zero, Op, Src),
%%%% trans_fp(I, Relocs1).
%%

%%
%% fstore
%%
trans_fstore(I, Builder, SymTab) ->
  {BaseRef, SymTab1} = load_opnd(hipe_rtl:fstore_base(I), Builder, SymTab),
  {OffsetRef, SymTab2} = load_opnd(hipe_rtl:fstore_offset(I), Builder, SymTab1),
  {SrcRef, SymTab2} = load_opnd(hipe_rtl:fstore_src(I), Builder, SymTab2),
  ValueRef = llevm:'LLVMBuildAdd'(Builder, BaseRef, OffsetRef, ""),
  PtrRef = llevm:'LLVMBuildIntToPtr'(Builder, ValueRef, ?FLOAT_TYPE_P, ""),
  llevm:'LLVMBuildStore'(Builder, SrcRef, PtrRef),
  SymTab2.

%%
%% switch
%%
trans_switch(I, Builder, SymTab, Relocs, Data) ->
  RtlSrc = hipe_rtl:switch_src(I),
  {SrcRef, SymTab1} = load_opnd(RtlSrc, Builder, SymTab),
  Labels = hipe_rtl:switch_labels(I),
  SortOrder = hipe_rtl:switch_sort_order(I),
  NrLabels = length(Labels),
  TableType = llevm:'LLVMArrayType'(?BYTE_TYPE_P, NrLabels),
  %% Create the jump table
  TableName = "table_"++integer_to_list(hipe_gensym:new_label(llvm)),
  Module = symtab_fetch(modRef, SymTab1),
  PtrRef = llevm:'LLVMAddGlobal'(Module, TableType, TableName),
  {Value, SymTab2} = indirect_create_const(Labels,  SymTab1),
  llevm:'LLVMSetInitializer'(PtrRef, Value),
  llevm:'LLVMSetGlobalConstant'(PtrRef, true),
  %% Create the indirectbr instruction 
  OffsetConst = llevm:'LLVMConstInt'(?WORD_TYPE, 0, true),
  PtrRef2 = llevm:'LLVMBuildGEP'(Builder, PtrRef, {OffsetConst, SrcRef}, 2, ""),
  ValueRef = llevm:'LLVMBuildLoad'(Builder, PtrRef2, ""),
  ValueRef2 = llevm:'LLVMBuildIndirectBr'(Builder, ValueRef, NrLabels),
  SymTab3 = indirect_add_dest(ValueRef2, Labels, SymTab2),

  %% Create New Data
  LMap = [{label, L} || L <- Labels],
  %% Update data with the info for the jump table
  {Data1, JTabLab} =
    case hipe_rtl:switch_sort_order(I) of
      [] ->
        hipe_consttab:insert_block(Data, word, LMap);
      SortOrder ->
        hipe_consttab:insert_sorted_block(Data, word, LMap, SortOrder)
    end,
  Relocs1 = relocs_store(TableName, {switch, {TableType, Labels, NrLabels,
                                    SortOrder}, JTabLab}, Relocs),
  {SymTab3, Relocs1, Data1}.

indirect_create_const(Labels, SymTab) ->
  Function = symtab_fetch_fun(SymTab),
  {Blocks, SymTab1} = create(Labels, Function, SymTab, []),
  ValueRef = llevm:'LLVMConstArray'(?BYTE_TYPE_P, list_to_tuple(Blocks),
                                    length(Blocks)),
  {ValueRef, SymTab1}.

%%%%
create([], _Function, SymTab, Acc) ->
  {lists:reverse(Acc), SymTab};
create([L|Ls], Function,  SymTab, Acc) ->
  {BBRef, SymTab1} = load_label(L, SymTab),
  ValueRef = llevm:'LLVMBlockAddress'(Function, BBRef),
  create(Ls, Function, SymTab1, [ValueRef|Acc]).

indirect_add_dest(_, [], SymTab) -> SymTab;
indirect_add_dest(IndirectRef, [L|Ls], SymTab) ->
  %% XXX: Maybe no update of symtab is needed!
  {BBRef, SymTab1} = load_label(L,  SymTab),
  llevm:'LLVMAddDestination'(IndirectRef, BBRef),
  indirect_add_dest(IndirectRef, Ls, SymTab1).
  

%%------------------------------------------------------------------------------
%% @doc In order to pin precoloured registers to physical registers we pass
%% to each call the precoloured registers as the first ?NR_PINNED_REGS args and
%% return them as the first ?NR_PINNED_REGS return values. The HiPE cc11 that
%% is defined to LLVM will assure that the correct values of the precoloured
%% registers will be in the corresponding physical registers when needed.
%%------------------------------------------------------------------------------
pin_precoloured_regs(Code, Params) ->
  Precoloured = find_precoloured_registers(),
  Params1 = Precoloured++Params,
  Code1 = [change_call(I, Precoloured) || I <- Code],
  {Code1, Params1}.

%% Append precoloured registers to arguments and return values of all
%% functions. In order to simplify the type checking, we assume that all
%% functions return ?FUN_RETURN_TYPE. Atom 'none' is used just as a dummy
%% return value in order to assure this.
change_call(I, Precoloured) ->
  case I of
    #call{} ->
      ArgList = hipe_rtl:call_arglist(I),
      DstList = hipe_rtl:call_dstlist(I),
      Dummy = case DstList of
        [] -> [none];
        _ -> []
      end,
      I1 = hipe_rtl:call_arglist_update(I, Precoloured++ArgList),
      hipe_rtl:call_dstlist_update(I1, Precoloured++Dummy++DstList);
    #enter{} ->
      ArgList = hipe_rtl:enter_arglist(I),
      I1 = hipe_rtl:enter_arglist_update(I, Precoloured++ArgList),
      hipe_rtl:enter_dstlist_update(I1, [none|Precoloured]);
    #return{} ->
      RetList = hipe_rtl:return_varlist(I),
      hipe_rtl:return_varlist_update(I, Precoloured++RetList);
    Other -> Other
  end.

find_precoloured_registers() ->
  [hipe_rtl:mk_reg((?ARCH_REGISTERS:heap_pointer())),
   hipe_rtl:mk_reg((?ARCH_REGISTERS:proc_pointer()))].

%%
%%%% @doc When a call has a fail continuation label it must be extended with a
%%%% normal continuation label to go with the LLVM's invoke instruction.
%%%% FailLabels is the list of labels of all fail blocks, which is needed to be
%%%% declared as landing pads. Also we must go to fail labels and add a call to
%%%% hipe_bifs:llvm_fix_pinned_regs:0 in order to avoid the reloading of old
%%%% values of pinned registers (This happens because at fail labels, the result
%%%% of an invoke instruction is no available, and we cannot get the correct
%%%% values of pinned registers). Finnaly when there are stack arguments the stack
%%%% needs to be readjusted.

%%fix_invoke_call(I, FailLabel, FailLabels) ->
%%  NewLabel = hipe_gensym:new_label(llvm),
%%  NewCall1 =  hipe_rtl:call_normal_update(I, NewLabel),
%%
%%create_fail_blocks(Label, FailLabels, Acc) ->
%%  case lists:keytake(Label, 1, FailLabels) of
%%    false ->
%%      Acc;
%%    {value, {Label, FailLabel, SpAdj}, RestFailLabels} ->
%%      I1 = hipe_llvm:mk_label(FailLabel),
%%      LP = #llvm_landingpad{},
%%      I2 =
%%        case SpAdj>0 of
%%          true ->
%%            StackPointer = ?ARCH_REGISTERS:reg_name(?ARCH_REGISTERS:sp()),
%%            hipe_llvm:mk_adj_stack(integer_to_list(SpAdj), StackPointer,
%%                                   ?WORD_TYPE);
%%          false -> []
%%        end,
%%      T1 = mk_temp(),
%%      FixedRegs = fixed_registers(),
%%      I3 = hipe_llvm:mk_call(T1, false, "cc 11", [], ?FUN_RETURN_TYPE,
%%                          "@hipe_bifs.llvm_fix_pinned_regs.0", [], []),
%%      I4 = store_fixed_regs(FixedRegs, T1),
%%      I5 = hipe_llvm:mk_br("%"++Label),
%%      Ins = lists:flatten([I5, I4, I3, I2, LP,I1]),
%%      create_fail_blocks(Label, RestFailLabels, Ins ++ Acc)
%%  end.
%%


%%------------------------------------------------------------------------------
%% Translation of Names
%%------------------------------------------------------------------------------

%% @doc create an acceptable LLVM identifier
make_llvm_id(Name) ->
  case Name of
    "" -> "Empty";
    Other -> lists:flatten(lists:map(fun llvm_id/1, Other))
  end.

%%
llvm_id(C) when C==46; C>47 andalso C<58; C>64 andalso C<91; C==95;
                C>96 andalso C<123 -> C;
llvm_id(C) ->
 io_lib:format("_~2.16.0B_",[C]).

%% @doc Fix F in MFA tuple to acceptable LLVM identifier (case of closure).
fix_mfa_name(Fun) ->
  {Mod_Name, Closure_Name, Arity} = Fun,
  Fun_Name = mkClosureName(Closure_Name),
  {Mod_Name, Fun_Name, Arity}.


%% @doc Create an acceptable LLVM identifier for an MFA
mkMFAName({M,F,A}) ->
  N = atom_to_list(M)++"."++atom_to_list(F)++"."++integer_to_list(A),
  make_llvm_id(N).

%% @doc Make an acceptable LLVM identifier for a closure name
mkClosureName(ClosureName) ->
  CN = atom_to_list(ClosureName),
  list_to_atom(make_llvm_id(CN)).

mkLabelName(N) ->
  "L" ++ integer_to_list(N).

%% mkJumpLabelName(N) ->
%%  "%L" ++ integer_to_list(N).

mkConstLabelName(N) ->
  "DL" ++ integer_to_list(N).

mkAtomName(Atom) ->
  "ATOM_" ++ make_llvm_id(atom_to_list(Atom)).

mkVarName(N) ->
  "var_" ++ integer_to_list(N).

mkRegName(N) ->
  "reg_" ++ integer_to_list(N).

mkFRegName(N) ->
  "freg_" ++ integer_to_list(N).

%%%%----------------------------------------------------------------------------
%%%%------------------- Translation of Operands ---------------------------------
%%%%----------------------------------------------------------------------------

store_float(ValueRef, Ptr, Builder, SymTab) ->
  FReg = hipe_rtl:fpreg_index(Ptr),
  case symtab_fetch({fpreg, FReg}, SymTab) of
    undefined ->
      %% Createa an alloca at the Entry block
      CurrentBBRef = symtab_fetch_bb(SymTab),
      Function = symtab_fetch_fun(SymTab),
      EntryBBRef = llevm:'LLVMGetEntryBasicBlock'(Function),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBBRef),
      FRegName = mkFRegName(FReg),
      PtrRef = llevm:'LLVMBuildAlloca'(Builder, ?FLOAT_TYPE, FRegName),
      SymTab1 = symtab_insert({fpreg, FReg}, PtrRef, SymTab),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, CurrentBBRef),
      %% Store the value
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab1;
    PtrRef ->
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab
  end.

store_opnd(ValueRef, Ptr, Builder, SymTab) ->
  case hipe_rtl:is_var(Ptr) of
    true -> store_var(ValueRef, Ptr, Builder, SymTab);
    false ->
      case hipe_rtl:is_reg(Ptr) of
        true ->
          case isPrecoloured(Ptr) of
            false ->
              store_register(ValueRef, Ptr, Builder, SymTab);
            true ->
              store_precoloured_register(ValueRef, Ptr, Builder, SymTab)
          end;
        false ->
          case hipe_rtl:is_fpreg(Ptr) of
            true -> store_freg(ValueRef, Ptr, Builder, SymTab);
            false ->
              exit({?MODULE, store_opnd, {"bad RTL arg",Ptr}})
          end
      end
  end.

store_var(ValueRef, Ptr, Builder, SymTab) ->
  Var = hipe_rtl:var_index(Ptr),
  case symtab_fetch({var, Var}, SymTab) of
    undefined ->
      %% Createa an alloca at the Entry block
      CurrentBBRef = symtab_fetch_bb(SymTab),
      Function = symtab_fetch_fun(SymTab),
      EntryBBRef = llevm:'LLVMGetEntryBasicBlock'(Function),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBBRef),
      VarName = mkVarName(Var),
      PtrRef = llevm:'LLVMBuildAlloca'(Builder, ?WORD_TYPE, VarName),
      SymTab1 = symtab_insert({var, Var}, PtrRef, SymTab),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, CurrentBBRef),
      %% Store the value
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab1;
    PtrRef ->
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab
  end.

store_freg(ValueRef, Ptr, Builder, SymTab) ->
  FReg = hipe_rtl:fpreg_index(Ptr),
  case symtab_fetch({fpreg, FReg}, SymTab) of
    undefined ->
      %% Createa an alloca at the Entry block
      CurrentBBRef = symtab_fetch_bb(SymTab),
      Function = symtab_fetch_fun(SymTab),
      EntryBBRef = llevm:'LLVMGetEntryBasicBlock'(Function),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBBRef),
      FRegName = mkFRegName(FReg),
      PtrRef = llevm:'LLVMBuildAlloca'(Builder, ?FLOAT_TYPE, FRegName),
      SymTab1 = symtab_insert({fpreg, FReg}, PtrRef, SymTab),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, CurrentBBRef),
      %% Store the value
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab1;
    PtrRef ->
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab
  end.

store_register(ValueRef, Ptr, Builder, SymTab) ->
  Reg = hipe_rtl:reg_index(Ptr),
  case symtab_fetch({reg, Reg}, SymTab) of
    undefined ->
      %% Createa an alloca at the Entry block
      CurrentBBRef = symtab_fetch_bb(SymTab),
      Function = symtab_fetch_fun(SymTab),
      EntryBBRef = llevm:'LLVMGetEntryBasicBlock'(Function),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBBRef),
      RegName = mkRegName(Reg),
      PtrRef = llevm:'LLVMBuildAlloca'(Builder, ?WORD_TYPE, RegName),
      SymTab1 = symtab_insert({reg, Reg}, PtrRef, SymTab),
      llevm:'LLVMPositionBuilderAtEnd'(Builder, CurrentBBRef),
      %% Store the value
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab1;
    PtrRef ->
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
      SymTab
  end.

store_precoloured_register(ValueRef, Ptr, Builder, SymTab) ->
  Reg = hipe_rtl:reg_index(Ptr),
  case ?ARCH_REGISTERS:proc_offset(Reg) of
    false ->
      store_register(ValueRef, Ptr, Builder, SymTab);
    Offset ->
      BaseReg = hipe_rtl:mk_reg(?ARCH_REGISTERS:proc_pointer()),
      %%RegName = ?ARCH_REGISTERS:reg_name(Reg),
      {PtrRef, SymTab1} = load_register(BaseReg, Builder, SymTab),
      PtrRef1 = llevm:'LLVMBuildIntToPtr'(Builder, PtrRef, ?WORD_TYPE_P, ""),
      OffsetConst = llevm:'LLVMConstInt'(?WORD_TYPE, Offset div (?WORD_WIDTH
            div 8), true),
      PtrRef2 = llevm:'LLVMBuildGEP'(Builder, PtrRef1, {OffsetConst},1,""),
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef2),
      SymTab1
  end.

load_float(Ptr, Builder, SymTab) ->
  case hipe_rtl:is_const_label(Ptr) of
    true ->
      ConstLabel = hipe_rtl:const_label_label(Ptr),
      case symtab_fetch({const_label, ConstLabel}, SymTab) of
        undefined ->
          %% Declare a global constant and convert the pointer to integer
          Module = symtab_fetch(modRef, SymTab),
          CLName = mkConstLabelName(ConstLabel),
          PtrRef1 = llevm:'LLVMAddGlobal'(Module, ?BYTE_TYPE, CLName),
          llevm:'LLVMSetGlobalConstant'(PtrRef1, true),
          OffsetConst = llevm:'LLVMConstInt'(?BYTE_TYPE, ?FLOAT_OFFSET, true),
          PtrRef2 = llevm:'LLVMBuildGEP'(Builder, PtrRef1, {OffsetConst}, 1, ""),
          ValueRef = llevm:'LLVMConstPtrToInt'(PtrRef2, ?FLOAT_TYPE),
          ValueRef1 = llevm:'LLVMBuildLoad'(Builder, ValueRef, ""),
          %% XXX: can a const label be used for float and non float instructions?
          SymTab1 = symtab_insert({const_label, ConstLabel}, ValueRef1, SymTab),
          {ValueRef1, SymTab1};
        ValueRef ->
          {ValueRef, SymTab}
      end;
    false ->
      load_opnd(Ptr, Builder, SymTab)
  end.

load_opnd(Ptr, Builder, SymTab) ->
  case hipe_rtl:is_imm(Ptr) of
    true -> load_imm(Ptr, SymTab);
    false ->
      case hipe_rtl:is_const_label(Ptr) of
        true -> load_const_label(Ptr, SymTab);
        false ->
          case hipe_rtl:is_var(Ptr) of
            true -> load_var(Ptr, Builder, SymTab);
            false ->
              case hipe_rtl:is_reg(Ptr) of
                true ->
                  case isPrecoloured(Ptr) of
                    true ->
                      load_precoloured_register(Ptr, Builder, SymTab);
                    false ->
                      load_register(Ptr, Builder, SymTab)
                  end;
                false ->
                  case hipe_rtl:is_fpreg(Ptr) of
                    true -> load_freg(Ptr, Builder, SymTab);
                    false ->
                      exit({?MODULE, load_opnd, {"bad RTL arg",Ptr}})
                  end
              end
          end
      end
  end.


load_imm(Ptr, SymTab) ->
  %% Just create the constant
  Value = hipe_rtl:imm_value(Ptr),
  ValueRef = 
    case Value >= 0 of
      true -> llevm:'LLVMConstInt'(?WORD_TYPE, Value, false);
      false ->
        PosValue = abs(Value),
        ValueRef1 = llevm:'LLVMConstInt'(?WORD_TYPE, PosValue, false),
        llevm:'LLVMConstNeg'(ValueRef1)
    end,
  {ValueRef, SymTab}.

load_const_label(Ptr, SymTab) ->
  ConstLabel = hipe_rtl:const_label_label(Ptr),
  case symtab_fetch({const_label, ConstLabel}, SymTab) of
    undefined ->
      %% Declare a global constant and convert the pointer to integer
      Module = symtab_fetch(modRef, SymTab),
      CLName = mkConstLabelName(ConstLabel),
      PtrRef = llevm:'LLVMAddGlobal'(Module, ?BYTE_TYPE, CLName),
      llevm:'LLVMSetGlobalConstant'(PtrRef, true),
      ValueRef = llevm:'LLVMConstPtrToInt'(PtrRef, ?WORD_TYPE),
      SymTab1 = symtab_insert({const_label, ConstLabel}, ValueRef, SymTab),
      {ValueRef, SymTab1};
    ValueRef ->
      {ValueRef, SymTab}
  end.

load_var(Ptr, Builder, SymTab) ->
  Var = hipe_rtl:var_index(Ptr),
  case symtab_fetch({var, Var}, SymTab) of
    undefined ->
      erlang:display(error_uninitialized_var);
    ValueRef ->
      %% Load the variable
      VarName = mkVarName(Var),
      ValueRef1 = llevm:'LLVMBuildLoad'(Builder, ValueRef, VarName),
      {ValueRef1, SymTab}
  end.


load_register(Ptr, Builder, SymTab) ->
    Reg = hipe_rtl:reg_index(Ptr),
    case symtab_fetch({reg, Reg}, SymTab) of
      undefined ->
        erlang:display(skata_uninitialized_reg);
      PtrRef ->
        %% Load the register
        RegName = mkRegName(Reg),
        ValueRef = llevm:'LLVMBuildLoad'(Builder, PtrRef, RegName),
        {ValueRef, SymTab}
    end.

load_precoloured_register(Ptr, Builder, SymTab) ->
  Reg = hipe_rtl:reg_index(Ptr),
  case ?ARCH_REGISTERS:proc_offset(Reg) of
    false ->
      load_register(Ptr, Builder, SymTab);
    Offset ->
      BaseReg = hipe_rtl:mk_reg((?ARCH_REGISTERS:proc_pointer())),
      RegName = mkRegName(Offset),
      {PtrRef, SymTab1} = load_register(BaseReg, Builder, SymTab),
      PtrRef1 = llevm:'LLVMBuildIntToPtr'(Builder,PtrRef, ?WORD_TYPE_P,""),
                         %%%XXX: ERROR
      OffsetConst = llevm:'LLVMConstInt'(?WORD_TYPE, Offset div (?WORD_WIDTH
            div 8), true),
      PtrRef2 = llevm:'LLVMBuildGEP'(Builder, PtrRef1,{OffsetConst},1, ""),
      ValueRef = llevm:'LLVMBuildLoad'(Builder, PtrRef2, RegName),
      {ValueRef, SymTab1}
  end.

load_freg(Ptr, Builder, SymTab) ->
  FReg = hipe_rtl:fpreg_index(Ptr),
  case symtab_fetch({fpreg, FReg}, SymTab) of
    undefined ->
      erlang:display(error_uninitialized_freg);
    PtrRef ->
      %% Load the variable
      FRegName = mkFRegName(FReg),
      ValueRef = llevm:'LLVMBuildLoad'(Builder, PtrRef, FRegName),
      {ValueRef, SymTab}
  end.

load_label(Label, SymTab) ->
  case symtab_fetch({label, Label}, SymTab) of
    undefined ->
      Function = symtab_fetch_fun(SymTab),
      BBRef = llevm:'LLVMAppendBasicBlock'(Function, mkLabelName(Label)),
      SymTab1 = symtab_insert({label, Label}, BBRef, SymTab),
      {BBRef, SymTab1};
    BBRef ->
      {BBRef, SymTab}
  end.


load_call(Name, RetType, ArgsType, ArgsNr, CC, SymTab) ->
  case symtab_fetch({call, Name}, SymTab) of
    undefined ->
      Module = symtab_fetch_mod(SymTab),
      FunType = llevm:'LLVMFunctionType'(RetType, ArgsType, ArgsNr, false),
      Function = llevm:'LLVMAddFunction'(Module, Name, FunType),
      case CC of
        [] -> ok;
        cc11 -> llevm:'LLVMSetFunctionCallConv'(Function, 11)
      end,
      SymTab1 = symtab_insert({call, Name}, Function, SymTab),
      {Function, SymTab1};
    Function ->
      {Function, SymTab}
  end.



%%%%------------------------------------------------------------------------------
%%%% Translation of operators
%%%%------------------------------------------------------------------------------


trans_prim_op(Op) ->
 case Op of
   '+' -> "bif_add";
   '-' -> "bif_sub";
   '*' -> "bif_mul";
   'div' -> "bif_div";
   '/' -> "bif_div";
   Other -> atom_to_list(Other)
 end.

trans_rel_op(Op) ->
  case Op of
    eq -> ?LLVMIntEQ;
    ne -> ?LLVMIntNE;
    gtu -> ?LLVMIntUGT;
    geu -> ?LLVMIntUGE;
    ltu -> ?LLVMIntULT;
    leu -> ?LLVMIntULE;
    gt -> ?LLVMIntSGT;
    ge -> ?LLVMIntSGE;
    lt -> ?LLVMIntSLT;
    le -> ?LLVMIntSLE
  end.

trans_alub_op(I, Sign) ->
  Op =
    case hipe_rtl:alub_op(I) of
      add -> "add";
      mul -> "mul";
      sub -> "sub";
      Other ->
        exit({?MODULE, trans_alub_op, {"Unknown alub operator", Other}})
    end,
  S =
    case Sign of
      signed -> "s";
      unsigned -> "u"
    end,
  Type = integer_to_list(?WORD_WIDTH),
  lists:concat(["llvm.", S, Op, ".with.overflow.i", Type]).

%%
%% Relocation Specific Stuff
%%

%% @doc Declaration of a variable for a table with the labels of all closure
%% calls in the code
declare_closures(Relocs, SymTab) ->
  Relocs1 = relocs_to_list(Relocs),
  ClosureLabels = lists:filter(fun is_closure_label/1, Relocs1),
  {LabelList, ArityList} = lists:unzip(
                             [{Label, A} ||
                               {_, {closure_label, Label, A}} <-
                               ClosureLabels]),
  NrLabels = length(LabelList),
  TableType = llevm:'LLVMArrayType'(?BYTE_TYPE_P, NrLabels),
  TableName = "table_closures",
  Module = symtab_fetch(modRef, SymTab),
  PtrRef = llevm:'LLVMAddGlobal'(Module, TableType, TableName),
  {ValueRef, SymTab1} = indirect_create_const(LabelList, SymTab),
  llevm:'LLVMSetLinkage'(PtrRef, ?LLVMExternalLinkage),
  llevm:'LLVMSetInitializer'(PtrRef, ValueRef),
  llevm:'LLVMSetGlobalConstant'(PtrRef, true),
  Relocs2 = relocs_store(TableName, {table_closures, ArityList},
                          Relocs),
  {Relocs2, SymTab1}.

is_closure_label( {_,{closure_label,_, _}}) -> true;
is_closure_label(_) -> false.

%%%%------------------------------------------------------------------------------
%%%% Miscellaneous Functions
%%%%------------------------------------------------------------------------------
type_from_size(Size) ->
 case Size of
   byte -> llevm:'LLVMInt8Type'();
   int16 -> llevm:'LLVMInt16Type'();
   int32 -> llevm:'LLVMInt32Type'();
   word -> ?WORD_TYPE
 end.

reverse_stack_args(ArgList) ->
  case erlang:length(ArgList) > ?NR_PINNED_REGS + ?NR_ARG_REGS of
    false -> ArgList;
    true ->
      {RegisterArgs, StackArgs} = lists:split(?NR_PINNED_REGS+?NR_ARG_REGS, ArgList),
      RegisterArgs ++ lists:reverse(StackArgs)
  end.

symtab_init() -> dict:new().

symtab_insert(Key, Value, SymTab) ->
  dict:store(Key, Value, SymTab).

symtab_fetch(Key, SymTab) ->
  try dict:fetch(Key, SymTab)
  catch
    _:_ -> undefined
  end.

symtab_fetch_bb(SymTab) ->
  case symtab_fetch(bbRef, SymTab) of
    undefined -> exit({error, symtab_fetch_bb, no_bb_in_symtab});
    BBRef -> BBRef
  end.

symtab_fetch_fun(SymTab) ->
  case symtab_fetch(funRef, SymTab) of
    undefined -> exit({error, symtab_fetch_fun, no_fun_in_symtab});
    Function -> Function
  end.

symtab_fetch_mod(SymTab) ->
  case symtab_fetch(modRef, SymTab) of
    undefined -> exit({error, symtab_fetch_mod, no_mod_in_symtab});
    Module -> Module
  end.

relocs_init() -> dict:new().

relocs_store(Key, Value, Relocs) ->
    dict:store(Key, Value, Relocs).

relocs_to_list(Relocs) -> dict:to_list(Relocs).
%%dict_fetch(Key, dict) ->
%%  try dict:fetch(Key, dict)
%%  catch
%%    _:_ -> undefined
%%  end.

find_first_label([]) ->
  exit({?MODULE, find_first_label, "Empty Code"});
find_first_label(Code) ->
  case I=hd(Code) of
    #label{} ->
      hipe_rtl:label_name(I);
    _ ->
      exit({?MODULE, find_first_label, "First instruction is not a
                                        label"})
  end.

isPrecoloured(X) -> hipe_rtl_arch:is_precoloured(X).

%% Print RTL to file
print_rtl(Code, FunName) ->
  {ok, File_rtl} = file:open(atom_to_list(FunName) ++ ".rtl", [write]),
  hipe_rtl:pp(File_rtl, Code),
  file:close(File_rtl).
