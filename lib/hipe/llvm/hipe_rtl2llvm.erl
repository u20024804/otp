%% -*- erlang-indent-level: 2 -*-

%%TODO:
%% -- Function Definition
%% -- Inline ASM stack adjustment
%% -- GEP Instruction
%% -- Constants
%% -- Relocs
%% -- Switches
%% -- Floating Point
-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").

-export([translate/2,
         fix_mfa_name/1]).

-include("../rtl/hipe_rtl.hrl").
-include("../rtl/hipe_literals.hrl").
-include("hipe_llvm.hrl").
-include("hipe_llvm_arch.hrl").
-include("llevm.hrl").

-define(WORD_TYPE, llevm:'LLVMInt64Type'()).
-define(WORD_TYPE_P, llevm:'LLVMPointerType'(?WORD_TYPE, 0)).
-define(FLOAT_TYPE, llevm:'LLVMDoubleType'()).
-define(FLOAT_TYPE_P, llevm:'LLVMPointerType'(?FLOAT_TYPE, 0)).
-define(BYTE_TYPE, llevm:'LLVMInt8Type'()).
-define(BYTE_TYPE_P, llevm:'LLVMPointerType'(?BYTE_TYPE, 0)).
-define(FUN_RETURN_TYPE, createTypeFunRet()).

createTypeFunRet() ->
  NR = ?NR_PINNED_REGS+1,
  RetType_ = lists:duplicate(NR, ?WORD_TYPE),
  RetType = list_to_tuple(RetType_),
  llevm:'LLVMStructType'(RetType, NR, false).

%%------------------------------------------------------------------------------
%% @doc Main function for translating an RTL function to LLVM Assembly. Takes as
%% input the RTL code and the variable indexes of possible garbage collection
%% roots and returns the corresponing LLVM, a dictionary with all the
%% relocations in the code and a hipe_constab() with informaton about data
%%------------------------------------------------------------------------------
translate(RTL, Roots) ->
  Fun = hipe_rtl:rtl_fun(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  Data0 = hipe_rtl:rtl_data(RTL),
  Code = hipe_rtl:rtl_code(RTL),
  {Code1, Params1} = fix_code(Code, Params),
  hipe_rtl:pp_instrs(standard_io, Code1),
  {ModName, _FunName, _Arity} = fix_mfa_name(Fun),
  %% Print RTL to file
  %% {ok, File_rtl} = file:open(atom_to_list(_FunName) ++ ".rtl", [write]),
  %% hipe_rtl:pp(File_rtl, RTL),
  %% file:close(File_rtl),
  ParamsNr = length(Params1),
  %% Init unique symbol generator and initialize the label counter to the last
  %% RTL label.
  hipe_gensym:init(llvm),
  {_, MaxLabel} = hipe_rtl:rtl_label_range(RTL),
  put({llvm,label_count}, MaxLabel+1),
  SymTab0 = symtab_init(),
  Relocs0 = relocs_init(),
  %% Put first label of RTL code in process dictionary
  find_code_entry_label(Code),
  %% Initialize relocations symbol dictionary
  Ctx = llevm:'LLVMGetGlobalContext'(),
  erlang:display(Ctx),
  ModRef = llevm:'LLVMModuleCreateWithName'(ModName),
  FunTypeRef = llevm:'LLVMFunctionType'(?FUN_RETURN_TYPE,
    create_type_fun_params(ParamsNr), ParamsNr, false),
  FunRef = llevm:'LLVMAddFunction'(ModRef, mkMFAName(Fun), FunTypeRef),
  SymTab1 = symtab_insert(funRef, FunRef, SymTab0),
  SymTab2 = symtab_insert(modRef, ModRef, SymTab1),
  llevm:'LLVMSetFunctionCallConv'(FunRef, 11),
  llevm:'LLVMSetGC'(FunRef, "erlang_gc"),
  %%Mp = llevm:'LLVMAddFunctionAttr'(FunRef, ?LLVMNoRedZoneAttribute),
  %%erlang:display(Mp),
  llevm:'LLVMAddFunctionAttr'(FunRef, ?LLVMNoUnwindAttribute),
  BuildRef0 = llevm:'LLVMCreateBuilderInContext'(Ctx),
  EntryBB = llevm:'LLVMAppendBasicBlock'(FunRef, "Entry"),
  llevm:'LLVMPositionBuilderAtEnd'(BuildRef0, EntryBB),
  SymTab3 = symtab_insert(bbRef, EntryBB, SymTab2),
  SymTab4 = store_params(Params1, FunRef, BuildRef0, SymTab3),
  {BuildRef1, _Data1, SymTab5, Relocs1} =
    translate_instr_list(Code1, BuildRef0, Data0, SymTab4, Relocs0),
  _SymTab6 = declare_roots(Roots, BuildRef1, SymTab5),
  io:format("Relocations are ~w:~n", [Relocs1]),
  io:format("RTL2LLVM Finished~n"),
  llevm:'LLVMWriteBitcodeToFile'(ModRef, "foo.bc"),
  llevm:'LLVMDumpModule'(ModRef),
  ok.


%% Create the type of the function parameters
create_type_fun_params(ParamsNr) ->
  ParamsType = lists:duplicate(ParamsNr, ?WORD_TYPE),
  list_to_tuple(ParamsType).

%% Store function parameters to corresponding variables
store_params(Params, FunRef,  Builder, SymTab) ->
  Params1 = reverse_stack_args(Params),
  store_params(Params1, FunRef, Builder, SymTab, 0).

store_params([], _FunRef, _Builder, SymTab, _N) -> SymTab;
store_params([P|Ps], FunRef, Builder, SymTab, N) ->
  ParamRef = llevm:'LLVMGetParam'(FunRef, N),
  SymTab1 = store_opnd(ParamRef, P, Builder, SymTab),
  store_params(Ps, FunRef, Builder, SymTab1, N+1).

declare_roots([], _Builder, SymTab) -> SymTab;
declare_roots(Roots, Builder, SymTab) ->
  ModRef = symtab_fetch_mod(SymTab),
  %% Create Metadata reference
  MetadataRef = llevm:'LLVMAddGlobal'(ModRef, ?BYTE_TYPE_P, "gc_metadata"),
  llevm:'LLVMSetGlobalConstant'(MetadataRef, true),
  %% Create llvm.gcroot function reference
  RetType = llevm:'LLVMVoidType'(),
  Name = "llvm.gcroot",
  ArgsType = {
    llevm:'LLVMPointerType'(?BYTE_TYPE_P),
    ?BYTE_TYPE_P},
  FunTypeRef = llevm:'LLVMFunctionType'(RetType, ArgsType, 2, false),
  GCRootFunRef = llevm:'LLVMAddFunction'(ModRef, Name, FunTypeRef),
  %% Place builder to the end of entry block
  declare_roots(Roots, Builder, SymTab, GCRootFunRef, MetadataRef).

declare_roots([R|Rs], Builder, SymTab, GCRootFunRef, MetadataRef) ->
  Ptr = hipe_rtl:mk_var(R),
  {ValueRef, SymTab1} = load_opnd(Ptr, Builder, SymTab),
  llevm:'LLVMBuildCall'(Builder, GCRootFunRef, {ValueRef, MetadataRef}, 2,
                                  "GCRoot"),
  declare_roots(Rs, Builder, SymTab1, GCRootFunRef, MetadataRef).

%%
translate_instr_list([], Builder, Data, SymTab, Relocs) -> {Builder, Data, SymTab, Relocs};
translate_instr_list([I|Is], Builder, Data, SymTab, Relocs) ->
  {Data1, SymTab1, Relocs1} = translate_instr(I, Builder, Data, SymTab, Relocs),
  translate_instr_list(Is, Builder, Data1, SymTab1, Relocs1).

translate_instr(I, Builder, Data, SymTab, Relocs) ->
  erlang:display(I),
  case I of
    #alu{} ->
      SymTab1 = trans_alu(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
    #alub{} ->
      SymTab1 = trans_alub(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
    #branch{} ->
      SymTab1 = trans_branch(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
    #call{} ->
      {SymTab1, Relocs1} = case hipe_rtl:call_fun(I) of
        %% In AMD64 this instruction does nothing!
        %% TODO: chech use of fwait in other architectures!
        fwait ->
          {SymTab, Relocs};
        _ ->
          trans_call(I, Builder, SymTab, Relocs)
      end,
     {Data, SymTab1, Relocs1};
    %%   #comment{} ->
    #enter{} ->
      {SymTab1, Relocs1} = trans_enter(I, Builder, SymTab, Relocs),
      {Data, SymTab1, Relocs1};
    %%   #fconv{} ->
    %%   #fload{} ->
    %%   #fmove{} ->
    %%   #fp{} ->
    %%   #fp_unop{} ->
    %%   #fstore{} ->
    #goto{} ->
      SymTab1 = trans_goto(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
    #label{} ->
      SymTab1 = trans_label(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
    #load{} ->
      SymTab1 = trans_load(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
    #load_address{} ->
      {SymTab1, Relocs1} = trans_load_address(I, Builder, SymTab, Relocs),
      {Data, SymTab1, Relocs1};
    #load_atom{} ->
      {SymTab1, Relocs1} = trans_load_atom(I, Builder, SymTab, Relocs),
      {Data, SymTab1, Relocs1};
    #move{} ->
      SymTab1 = trans_move(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
    #return{} ->
      trans_return(I, Builder, SymTab),
      {Data, SymTab, Relocs};
    #store{} ->
      SymTab1 = trans_store(I, Builder, SymTab),
      {Data, SymTab1, Relocs};
      %%   #switch{} -> %% Only switch instruction updates Data
      _ -> {Data, SymTab, Relocs}
        %% Other ->
        %%   exit({?MODULE, translate_instr, {"unknown RTL instruction", Other}})
    end.




find_code_entry_label([]) ->
  exit({?MODULE, find_code_entry_label, "Empty Code"});
find_code_entry_label(Code) ->
  case I=hd(Code) of
    #label{} ->
      put(first_label, hipe_rtl:label_name(I));
    _ ->
      exit({?MODULE, find_code_entry_label, "First instruction is not a
          label"})
  end.

%%
%% alu
%%
trans_alu(I, Builder, SymTab) ->
  RtlDst = hipe_rtl:alu_dst(I),
  {SrcRef1, SymTab1} = load_opnd(hipe_rtl:alu_src1(I), Builder, SymTab),
  {SrcRef2, SymTab2} = load_opnd(hipe_rtl:alu_src1(I), Builder, SymTab1),
  io:format("lOADED OPERANS~n"),
  ValueRef =
    case hipe_rtl:alu_op(I) of
      'add' -> llevm:'LLVMBuildAdd'(Builder, SrcRef1, SrcRef2, "t");
      'sub' -> llevm:'LLVMBuildSub'(Builder, SrcRef1, SrcRef2, "t");
      'or'  -> llevm:'LLVMBuildOr'(Builder, SrcRef1, SrcRef2, "t");
      'and' -> llevm:'LLVMBuildAnd'(Builder, SrcRef1, SrcRef2, "t");
      'xor' -> llevm:'LLVMBuildXor'(Builder, SrcRef1, SrcRef2, "t");
      'sll' -> llevm:'LLVMBuildShl'(Builder, SrcRef1, SrcRef2, "t");
      'srl' -> llevm:'LLVMBuildLshr'(Builder, SrcRef1, SrcRef2, "t");
      'sra' -> llevm:'LLVMBuildAshr'(Builder, SrcRef1, SrcRef2, "t");
      'mul' -> llevm:'LLVMBuildMul'(Builder, SrcRef1, SrcRef2, "t");
      'fdiv' -> llevm:'LLVMBuildFdiv'(Builder, SrcRef1, SrcRef2, "t");
      'sdiv' -> llevm:'LLVMBuildSdiv'(Builder, SrcRef1, SrcRef2, "t");
      'srem' -> llevm:'LLVMBuildSrem'(Builder, SrcRef1, SrcRef2, "t");
    Other -> exit({?MODULE, trans_op, {"Unknown RTL Operator",Other}})
  end,
  store_opnd(ValueRef, RtlDst, Builder, SymTab2).

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
  {SrcRef1, SymTab1} = load_opnd(hipe_rtl:alub_src1(I), Builder, SymTab),
  {SrcRef2, SymTab2} = load_opnd(hipe_rtl:alub_src2(I), Builder, SymTab1),
  RtlDst = hipe_rtl:alub_dst(I),
  Name = trans_alub_op(I, Sign),
  {FunRef2, SymTab4} =
  case symtab_fetch({call, Name}, SymTab2) of
    undefined ->
      ModRef = symtab_fetch_mod(SymTab2),
      RetType = llevm:'LLVMStructType'(
        {?WORD_TYPE, llevm:'LLVMInt1Type'()}, 2, false),
      FunTypeRef = llevm:'LLVMFunctionType'(RetType,
        {?WORD_TYPE, ?WORD_TYPE}, 2, false),
      FunRef = llevm:'LLVMAddFunction'(ModRef, Name, FunTypeRef),
      SymTab3 = symtab_insert({call, Name}, FunRef, SymTab2),
      {FunRef, SymTab3};
    FunRef ->
      {FunRef, SymTab2}
  end,
  TempRef = llevm:'LLVMBuildCall'(Builder, FunRef2, {SrcRef1, SrcRef2}, 2,
    "OverflowTMP"),
  ResRef = llevm:'LLVMBuildExtractValue'(Builder, TempRef, 0, "result"),
  SymTab5 = store_opnd(ResRef, RtlDst, Builder, SymTab4),
  OverflowRef = llevm:'LLVMBuildExtractValue'(Builder, TempRef, 0, "overflow"),
  case hipe_rtl:alub_cond(I) of
    Op when Op =:= overflow orelse Op =:= ltu ->
      {TrueRef, SymTab6} = bbRef_from_label(hipe_rtl:alub_true_label(I),SymTab5),
      {FalseRef, SymTab7} = bbRef_from_label(hipe_rtl:alub_false_label(I), SymTab6);
    not_overflow ->
      {TrueRef, SymTab6} = bbRef_from_label(hipe_rtl:alub_false_label(I), SymTab5),
      {FalseRef, SymTab7} = bbRef_from_label(hipe_rtl:alub_true_label(I), SymTab6)
  end,
  llevm:'LLVMBuildCondBr'(Builder, OverflowRef, TrueRef, FalseRef),
  SymTab7.

trans_alub_op(I, Sign) ->
  Op =
    case hipe_rtl:alub_op(I) of
      add -> "llvm.sadd.with.overflow.";
      mul -> "llvm.smul.with.overflow.";
      sub -> "llvm.ssub.with.overflow.";
      Other ->
        exit({?MODULE, trans_alub_op, {"Unknown alub operator", Other}})
    end,
  S =
    case Sign of
      signed -> "s";
      unsigned -> "u"
    end,
  Type = integer_to_list(?WORD_WIDTH),
  lists:concat(["llvm.", S, Op, ".with.overflow.", Type]).


trans_alub_no_overflow(I, Builder, SymTab) ->
  %% alu
  AluI = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
                      hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  %% A trans_alu instruction cannot change relocations
  SymTab1 = trans_alu(AluI, Builder, SymTab),
  %% icmp
  %% Translate destination as src, to match with the semantic of instruction
  {DstRef, SymTab2} = load_opnd(hipe_rtl:alub_dst(I), Builder, SymTab1),
  Cond = trans_rel_op(hipe_rtl:alub_cond(I)),
  ZeroConst = llevm:'LLVMConstInt'(?WORD_TYPE, 0, true),
  IfRef = llevm:'LLVMBuildICmp'(Builder, Cond, DstRef, ZeroConst, ""),
  %% br
  {TrueBB, SymTab3} = bbRef_from_label(hipe_rtl:alub_true_label(I), SymTab2),
  {FalseBB, SymTab4} = bbRef_from_label(hipe_rtl:alub_false_label(I), SymTab3),
  llevm:'LLVMBuildCondBr'(Builder, IfRef, TrueBB, FalseBB),
  SymTab4.

bbRef_from_label(Label, SymTab) ->
  case symtab_fetch({label, Label}, SymTab) of
    undefined ->
      FunRef = symtab_fetch_fun(SymTab),
      BBRef = llevm:'LLVMAppendBasicBlock'(FunRef, mkLabelName(Label)),
      SymTab1 = symtab_insert({label, Label}, BBRef, SymTab),
      {BBRef, SymTab1};
    BBRef ->
      {BBRef, SymTab}
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

%%
%% branch
%%
trans_branch(I, Builder, SymTab) ->
  {SrcRef1, SymTab1} = load_opnd(hipe_rtl:branch_src1(I), Builder, SymTab),
  {SrcRef2, SymTab2} = load_opnd(hipe_rtl:branch_src2(I), Builder, SymTab1),
  Cond = trans_rel_op(hipe_rtl:branch_cond(I)),
  %% icmp
  IfRef = llevm:'LLVMBuildICmp'(Builder, Cond, SrcRef1, SrcRef2, ""),
  %% br
  {TrueBB, SymTab3} = bbRef_from_label(hipe_rtl:branch_true_label(I),SymTab2),
  {FalseBB, SymTab4} = bbRef_from_label(hipe_rtl:branch_false_label(I),
    SymTab3),
  llevm:'LLVMBuildCondBr'(Builder, IfRef, TrueBB, FalseBB),
  SymTab4.

%%%%
%%%% call
%%%%
trans_call(I, Builder, SymTab, Relocs) ->
  ArgList= reverse_stack_args(hipe_rtl:call_arglist(I)),
  RetList = hipe_rtl:call_dstlist(I),
  CallName = hipe_rtl:call_fun(I),
  {SymTab1, Relocs1} =  expose_closure(Builder, SymTab, CallName, ArgList, Relocs),
  %% Loading the arguments cannot change the SymTab, so we ignore it
  {ArgListRef, _} = lists:unzip([ load_opnd(X, Builder, SymTab1) || X<-ArgList ]),
  {FunRef, SymTab2, Relocs2} =  trans_call_name(Builder, SymTab, Relocs1, CallName, ArgList, RetList),
  SymTab8 = case hipe_rtl:call_fail(I) of
    [] -> %% Call Without Exception Handler
      RetStruct = llevm:'LLVMBuildCall'(Builder, FunRef, list_to_tuple(ArgListRef),
                                        length(ArgListRef), ""),
      store_call_retlist(RetStruct, RetList, Builder, SymTab2);
    FailLabel -> %% Call With Exception Handler
      ContLabel = hipe_rtl:call_continuation(I),
      {ContRef, SymTab3} = bbRef_from_label(ContLabel, SymTab2),
      {FailRef, SymTab4} = bbRef_from_label(FailLabel, SymTab3),
      RetStruct = llevm:'LLVMBuildInvoke'(Builder, FunRef, list_to_tuple(ArgListRef),
                                        length(ArgListRef), ContRef, FailRef, "callTmp"),
      BBRef = symtab_fetch_bb(SymTab2),
      NewFailLabel = hipe_gensym:new_label(llvm),
      SymTab5 = trans_label(hipe_rtl:mk_label(NewFailLabel), Builder, SymTab4),
      SymTab6 = create_new_fail_block(NewFailLabel, FailLabel, RetStruct, RetList, Builder, SymTab5),
      NewContLabel = hipe_gensym:new_label(llvm),
      SymTab7 = create_new_cont_block(NewContLabel, ContLabel, RetStruct,
                                      RetList, Builder, SymTab6),
      %%% XXX: UnNessecary /
      llevm:'LLVMPositionBuilderAtEnd'(Builder, BBRef),
      SymTab7
  end,
  {SymTab8, Relocs2}.


reverse_stack_args(ArgList) ->
  case erlang:length(ArgList) > ?NR_PINNED_REGS + ?NR_ARG_REGS of
    false -> ArgList;
    true ->
      {RegisterArgs, StackArgs} = lists:split(?NR_PINNED_REGS+?NR_ARG_REGS, ArgList),
      RegisterArgs ++ StackArgs
  end.

store_call_retlist(RetStruct, RetList, Builder, SymTab) ->
  store_call_retlist(RetStruct, RetList, Builder, SymTab, 0).

store_call_retlist(_RetStruct, [], _Builder, SymTab, _Num) -> SymTab;
store_call_retlist(RetStruct, [R|Rs], Builder, SymTab, Num) ->
  ValueRef = llevm:'LLVMBuildExtractValue'(Builder, RetStruct, Num, ""),
  SymTab1 = store_opnd(ValueRef, R, Builder, SymTab),
  store_call_retlist(RetStruct, Rs, Builder, SymTab1, Num+1).

create_new_fail_block(NewFailLabel, FailLabel, RetStruct, RetList, Builder, SymTab) ->
  SymTab1 = trans_label(hipe_rtl:mk_label(NewFailLabel), Builder, SymTab),
  %% Personality Function And Landing Pad
  {PersFunRef, SymTab2} = create_personality_function(SymTab1),
  LandPadRef = llevm:'LLVMBuildLandingPad'(Builder, llevm:'LLVMInt32Type'(),
                                          PersFunRef, 0, ""),
  llevm:'LLVMSetCleanup'(LandPadRef, true),
  %% hipe_bifs:llvm_fix_pinned_regs()
  {BifRetList, _} = lists:split(?NR_PINNED_REGS, RetList),
  {BifFunRef, SymTab3} = create_bif_pinned_regs(SymTab2, BifRetList),
  RetStruct = llevm:'LLVMBuildCall'(Builder, BifFunRef, {}, 0, ""),
  SymTab4 = store_call_retlist(RetStruct, BifRetList, Builder, SymTab3),
  trans_goto(hipe_rtl:mk_goto(FailLabel), Builder, SymTab4).

create_personality_function(SymTab) ->
  PersFnName = "__gcc_personality_v0",
  case symtab_fetch({call, PersFnName}, SymTab) of
    undefined ->
      ModRef = symtab_fetch_mod(SymTab),
      RetType = llevm:'LLVMInt32Type'(),
      ArgsType = {
        llevm:'LLVMInt32Type'(),
        llevm:'LLVMInt64Type'(),
        llevm:'LLVMPointerType'(llevm:'LLVMInt8Type'(), 0),
        llevm:'LLVMPointerType'(llevm:'LLVMInt8Type'(), 0)},
      FunTypeRef = llevm:'LLVMFunctionType'(RetType, ArgsType, 4, false),
      FunRef = llevm:'LLVMAddFunction'(ModRef, PersFnName, FunTypeRef),
      SymTab1 = symtab_insert({call, PersFnName}, FunRef, SymTab),
      {FunRef, SymTab1};
    FunRef ->
      {FunRef, SymTab}
  end.

create_bif_pinned_regs(SymTab, RetList) ->
  BifName = "hipe_bifs:llvm_fix_pinned_regs.0",
  case symtab_fetch({call, BifName}, SymTab) of
    undefined ->
      ModRef = symtab_fetch_mod(SymTab),
      RetTypeList = ([?WORD_TYPE || _ <- RetList]),
      RetType = llevm:'LLVMStructType'(list_to_tuple(RetTypeList),
                                      length(RetTypeList), false),
      ArgsType = {},
      FunTypeRef = llevm:'LLVMFunctionType'(RetType, ArgsType, 0, false),
      FunRef = llevm:'LLVMAddFunction'(ModRef, BifName, FunTypeRef),
      SymTab1 = symtab_insert({call, BifName}, FunRef, SymTab),
      {FunRef, SymTab1};
    FunRef ->
      {FunRef, SymTab}
  end.


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
     Label = hipe_gensym:new_label(llvm),
     FunRef = symtab_fetch_fun(SymTab),
     BBRef = llevm:'LLVMAppendBasicBlock'(FunRef, mkLabelName(Label)),
     SymTab1 = symtab_insert({label, Label}, BBRef, SymTab),
     llevm:'LLVMBuildBr'(Builder, BBRef),
     llevm:'LLVMPositionBuilderAtEnd'(Builder, BBRef),
     SymTab2 = symtab_insert(bbRef, BBRef, SymTab1),
     Relocs1 = relocs_store({CallName, Label}, {closure_label, Label,
                            length(CallArgs) - ?NR_ARG_REGS -?NR_PINNED_REGS},
                            Relocs),
    {SymTab2, Relocs1};
   false ->
    {SymTab, Relocs}
 end.

create_fun_decl(CallName, CallArgs, CallRet, SymTab) ->
  case symtab_fetch({call, CallName}, SymTab) of
    undefined ->
      ModRef = symtab_fetch_mod(SymTab),
      RetType = [ ?WORD_TYPE || _ <- CallRet ],
      RetType1 = llevm:'LLVMStructType'(list_to_tuple(RetType), length(RetType),
                                        false),
      ArgsType = [ ?WORD_TYPE || _ <- CallArgs ],
      FunTypeRef = llevm:'LLVMFunctionType'(RetType1, list_to_tuple(ArgsType),
                                            length(ArgsType), false),
      FunRef = llevm:'LLVMAddFunction'(ModRef, CallName, FunTypeRef),
      SymTab1 = symtab_insert({call, CallName}, FunRef, SymTab),
      {FunRef, SymTab1};
    FunRef ->
      {FunRef, SymTab}
  end.

%%
trans_call_name(Builder, SymTab, Relocs,  CallName, CallArgs, CallRet) ->
  case CallName of
    PrimOp when is_atom(PrimOp) ->
      LLVMName = trans_prim_op(PrimOp),
      {FunRef, SymTab1} = create_fun_decl(LLVMName, CallArgs, CallRet, SymTab),
      Relocs1 = relocs_store(LLVMName, {call, {bif, PrimOp,
                            length(CallArgs)-?NR_PINNED_REGS}}, Relocs),
      {FunRef, SymTab1, Relocs1};
    {M, F, A} when is_atom(M), is_atom(F), is_integer(A) ->
      LLVMName = fix_mfa_name({M,F,A}),
      {FunRef, SymTab1} = create_fun_decl(LLVMName, CallArgs, CallRet, SymTab),
       Relocs1 = relocs_store(LLVMName, {call, {M,F,A}}, Relocs),
       {FunRef, SymTab1, Relocs1};
    Reg ->
      case hipe_rtl:is_reg(Reg) of
        true -> %% In case of a closure call, the register holding the address
          %% of the closure must be converted to function type in
          %% order to make the call
          {RegRef, SymTab1} = load_opnd(Reg, Builder, SymTab),
          llevm:'LLVMBuildIntToPtr'(Builder, RegRef, ?WORD_TYPE_P,
                                    ""),
          RetType = [ ?WORD_TYPE || _ <- CallRet ],
          RetType1 = llevm:'LLVMStructType'(list_to_tuple(RetType), length(RetType),
                                            false),
          ArgsType = [ ?WORD_TYPE || _ <- CallArgs ],
          FunTypeRef = llevm:'LLVMFunctionType'(RetType1, list_to_tuple(ArgsType),
                                                length(ArgsType), false),
          FunTypePointer = llevm:'LLVMPointerType'(FunTypeRef, 0),
          FunRef = llevm:'LLVMBuildBitCast'(Builder, RegRef, FunTypePointer, ""),
          {FunRef, SymTab1};
        false ->
          exit({?MODULE, trans_call, {"Unimplemted Call to", CallName}})
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
  ArgList= reverse_stack_args(hipe_rtl:enter_arglist(I)),
  RetList = hipe_rtl:enter_dstlist(I),
  CallName = hipe_rtl:enter_fun(I),
  %% Loading the arguments cannot change the SymTab, so we ignore it
  {ArgListRef, _} = lists:unzip([ load_opnd(X, Builder, SymTab) || X<-ArgList ]),
  {FunRef, SymTab2, Relocs1} =  trans_call_name(Builder, SymTab, Relocs, CallName,
                                                ArgList, RetList),
  RetStruct = llevm:'LLVMBuildCall'(Builder, FunRef, list_to_tuple(ArgListRef),
                                        length(ArgListRef), ""),
  llevm:'LLVMBuildAggregateRet'(Builder, RetStruct, length(RetList)),
  {SymTab2, Relocs1}.
%%%%
%%%% fconv
%%%%
%%trans_fconv(I, Relocs) ->
%%  %% XXX: Can a fconv destination be a precoloured reg?
%%  RtlDst = hipe_rtl:fconv_dst(I),
%%  TmpDst = mk_temp(),
%%  {Src, I1} =  trans_float_src(hipe_rtl:fconv_src(I)),
%%  I2 = hipe_llvm:mk_conversion(TmpDst, sitofp, ?WORD_TYPE, Src, ?FLOAT_TYPE),
%%  I3 = store_float_stack(TmpDst, RtlDst),
%%  {[I3, I2, I1], Relocs}.
%%
%%
%%%% TODO: fload, fstore, fmove, and fp are almost the same with load,store,move
%%%% and alu. Maybe we should join them.
%%
%%%%
%%%% fload
%%%%
%%trans_fload(I, Relocs) ->
%%  RtlDst = hipe_rtl:fload_dst(I),
%%  RtlSrc = hipe_rtl:fload_src(I),
%%  _Offset = hipe_rtl:fload_offset(I),
%%  TmpDst = mk_temp(),
%%  {Src, I1} = trans_float_src(RtlSrc),
%%  {Offset, I2} = trans_float_src(_Offset),
%%  T1 = mk_temp(),
%%  I3 = hipe_llvm:mk_operation(T1, add, ?WORD_TYPE, Src, Offset, []),
%%  T2 = mk_temp(),
%%  I4 = hipe_llvm:mk_conversion(T2, inttoptr,  ?WORD_TYPE, T1, ?FLOAT_TYPE_P),
%%  I5 = hipe_llvm:mk_load(TmpDst, ?FLOAT_TYPE_P, T2, [], [], false),
%%  I6 = store_float_stack(TmpDst, RtlDst),
%%  {[I6, I5, I4, I3, I2, I1], Relocs}.
%%
%%%%
%%%% fmove
%%%%
%%trans_fmove(I, Relocs) ->
%%  RtlDst = hipe_rtl:fmove_dst(I),
%%  RtlSrc = hipe_rtl:fmove_src(I),
%%  {Src, I1} = trans_float_src(RtlSrc),
%%  I2 = store_float_stack(Src, RtlDst),
%%  {[I2, I1], Relocs}.
%%
%%%%
%%%% fp
%%%%
%%trans_fp(I, Relocs) ->
%%  %% XXX: Just copied trans_alu...think again..
%%  RtlDst = hipe_rtl:fp_dst(I),
%%  RtlSrc1 = hipe_rtl:fp_src1(I),
%%  RtlSrc2 = hipe_rtl:fp_src2(I),
%%  %% Destination cannot be a precoloured register
%%  TmpDst = mk_temp(),
%%  {Src1, I1} = trans_float_src(RtlSrc1),
%%  {Src2, I2} = trans_float_src(RtlSrc2),
%%  Op = trans_fp_op(hipe_rtl:fp_op(I)),
%%  I3 = hipe_llvm:mk_operation(TmpDst, Op, ?FLOAT_TYPE, Src1, Src2, []),
%%  I4 = store_float_stack(TmpDst, RtlDst),
%%  %% Synchronization for floating point exceptions
%%  I5 = hipe_llvm:mk_store(?FLOAT_TYPE, TmpDst, ?FLOAT_TYPE_P, "%exception_sync",
%%                          [] ,[], true),
%%  T1 = mk_temp(),
%%  I6 = hipe_llvm:mk_load(T1, ?FLOAT_TYPE_P, "%exception_sync", [], [] ,true),
%%  {[I6, I5, I4, I3, I2, I1], Relocs}.
%%
%%%%
%%%% fp_unop
%%%%
%%trans_fp_unop(I, Relocs) ->
%%  RtlDst = hipe_rtl:fp_unop_dst(I),
%%  RtlSrc = hipe_rtl:fp_unop_src(I),
%%  % Destination cannot be a precoloured register
%%  TmpDst = mk_temp(),
%%  {Src, I1} = trans_float_src(RtlSrc),
%%  Op =  trans_fp_op(hipe_rtl:fp_unop_op(I)),
%%  I2 = hipe_llvm:mk_operation(TmpDst, Op, ?FLOAT_TYPE, "0.0", Src, []),
%%  I3 = store_float_stack(TmpDst, RtlDst),
%%  {[I3, I2, I1], Relocs}.
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
%%%%
%%%% fstore
%%%%
%%trans_fstore(I, Relocs) ->
%%  Base = hipe_rtl:fstore_base(I),
%%  I1 = case isPrecoloured(Base) of
%%    true ->
%%      trans_fstore_reg(I, Relocs);
%%    false ->
%%      exit({?MODULE, trans_fstore ,{"Non Implemened yet", false}})
%%  end,
%%  I1.
%%
%%trans_fstore_reg(I, Relocs) ->
%%  {Base, I0}  = trans_reg(hipe_rtl:fstore_base(I), dst),
%%  T1 = mk_temp(),
%%  I1 = hipe_llvm:mk_load(T1, ?WORD_TYPE_P, Base, [],  [], false),
%%  {Offset, I2} = trans_src(hipe_rtl:fstore_offset(I)),
%%  T2 = mk_temp(),
%%  I3 = hipe_llvm:mk_operation(T2, add, ?WORD_TYPE, T1, Offset, []),
%%  T3 = mk_temp(),
%%  I4 = hipe_llvm:mk_conversion(T3, inttoptr, ?WORD_TYPE, T2, ?FLOAT_TYPE_P),
%%  {Value, I5} = trans_src(hipe_rtl:fstore_src(I)),
%%  I6 = hipe_llvm:mk_store(?FLOAT_TYPE, Value, ?FLOAT_TYPE_P, T3, [], [],
%%                          false),
%%  {[I6, I5, I4, I3, I2, I1, I0], Relocs}.
%%
%%
%% goto
%%
trans_goto(I, BuilderRef, SymTab) ->
  Label = hipe_rtl:goto_label(I),
  case symtab_fetch(Label, SymTab) of
    undefined ->
      FunRef = symtab_fetch_fun(SymTab),
      BBRef = llevm:'LLVMAppendBasicBlock'(FunRef, mkLabelName(Label)),
      SymTab1 = symtab_insert(Label, BBRef, SymTab),
      llevm:'LLVMBuildBr'(BuilderRef, BBRef),
      SymTab1;
    BBRef ->
      llevm:'LLVMBuildBr'(BuilderRef, BBRef),
      SymTab
  end.

%%
%% label
%%
trans_label(I, BuilderRef, SymTab) ->
 Label  = hipe_rtl:label_name(I),
 case symtab_fetch({label, Label}, SymTab) of
   undefined ->
    FunRef = symtab_fetch_fun(SymTab),
    BBRef = llevm:'LLVMAppendBasicBlock'(FunRef, mkLabelName(Label)),
    SymTab1 = symtab_insert({label, Label}, BBRef, SymTab),
    llevm:'LLVMPositionBuilderAtEnd'(BuilderRef, BBRef),
    symtab_insert(bbRef, BBRef, SymTab1);
  BBRef ->
    llevm:'LLVMPositionBuilderAtEnd'(BuilderRef, BBRef),
    SymTab
  end.

%%
%% load
%%
trans_load(I, Builder, SymTab) ->
  RtlDst = hipe_rtl:load_dst(I),
  {SrcRef, SymTab1} = load_opnd(hipe_rtl:load_src(I), Builder, SymTab),
  {OffsetRef, SymTab2} = load_opnd(hipe_rtl:load_offset(I), Builder, SymTab1),
  ValueRef = llevm:'LLVMBuildAdd'(Builder, SrcRef, OffsetRef, "tempAdd"),
  LoadedRef =
  case hipe_rtl:load_size(I) of
    word ->
      PtrRef = llevm:'LLVMBuildPtrToInt'(Builder, ValueRef, ?WORD_TYPE, "pointerTmp"),
      llevm:'LLVMBuildLoad'(Builder, PtrRef, "tempLoad");
    Size ->
      LoadType = type_from_size(Size),
      LoadTypeP = llevm:'LLVMPointerType'(LoadType, 0),
      PtrRef = llevm:'LLVMBuildPtrToInt'(Builder, ValueRef, LoadTypeP, "pointerTmp"),
      LoadedRef_ = llevm:'LLVMBuildLoad'(Builder, PtrRef, "tempLoad"),
      case hipe_rtl:load_sign(I) of
        signed -> llevm:'LLVMBuildSext'(Builder, LoadedRef_, ?WORD_TYPE,
            "convTemp");
        unsigned -> llevm:'LLVMBuildZext'(Builder, LoadedRef_, ?WORD_TYPE,
            "convTemp")
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
        {ValueRef, SymTab1} = load_opnd(RtlAddr, Builder, SymTab),
        {ValueRef, SymTab1, Relocs};
      closure  ->
        Closure = RtlAddr,
        case symtab_fetch({closure, Closure}, SymTab) of
          undefined ->
            %% Declare a global constant and convert the pointer to integer
            ModRef = symtab_fetch(modRef, SymTab),
            ClosureName = mkClosureName(Closure),
            PtrRef = llevm:'LLVMAddGlobal'(ModRef, ?BYTE_TYPE, ClosureName),
            llevm:'LLVMSetGlobalConstant'(PtrRef, true),
            ValueRef = llevm:'LLVMConstPtrToInt'(PtrRef, ?WORD_TYPE),
            SymTab1 = symtab_insert({closure, Closure}, ValueRef, SymTab),
            Relocs1 = relocs_store(ClosureName, {closure, Closure}, Relocs),
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
  {ValueRef , SymTab1} = trans_atom(Atom, SymTab),
  Dst = hipe_rtl:load_atom_dst(I),
  SymTab2 = store_opnd(ValueRef, Dst, Builder, SymTab1),
  AtomName = mkAtomName(Atom),
  Relocs1 = relocs_store(AtomName, {atom, Atom}, Relocs),
  {SymTab2, Relocs1}.


trans_atom(Atom, SymTab) ->
  case symtab_fetch({atom, Atom}, SymTab) of
    undefined ->
      %% Declare a global constant and convert the pointer to integer
      ModRef = symtab_fetch(modRef, SymTab),
      AtomName = mkAtomName(Atom),
      PtrRef = llevm:'LLVMAddGlobal'(ModRef, ?BYTE_TYPE, AtomName),
      llevm:'LLVMSetGlobalConstant'(PtrRef, true),
      ValueRef = llevm:'LLVMConstPtrToInt'(PtrRef, ?WORD_TYPE),
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
  RetListVR= [load_opnd(X, Builder, SymTab) || X<-RetList],
  {RetListValueRef, _}= lists:unzip(RetListVR),
  RetListValueRef1 = list_to_tuple(RetListValueRef),
  llevm:'LLVMBuildAggregateRet'(Builder, RetListValueRef1, length(RetList)).

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


%%%%
%%%% switch
%%%%
%%trans_switch(I, Relocs, Data) ->
%%  RtlSrc = hipe_rtl:switch_src(I),
%%  {Src, I1} = trans_src(RtlSrc),
%%  Labels = hipe_rtl:switch_labels(I),
%%  JumpLabels = lists:map(fun mk_jump_label/1, Labels),
%%  SortOrder = hipe_rtl:switch_sort_order(I),
%%  NrLabels = length(Labels),
%%  TableType = hipe_llvm:mk_array(NrLabels, ?BYTE_TYPE_P),
%%  TableTypeP = hipe_llvm:mk_pointer(TableType),
%%  TypedJumpLabels = lists:map(fun(X) -> {#llvm_label_type{}, X} end, JumpLabels),
%%  T1 = mk_temp(),
%%  {Src2, []} = trans_dst(RtlSrc),
%%  TableName = "table_"++tl(Src2),
%%  I2 = hipe_llvm:mk_getelementptr(T1, TableTypeP, "@"++TableName,
%%                                  [{?WORD_TYPE, "0"}, {?WORD_TYPE, Src}], false),
%%  T2 = mk_temp(),
%%  BYTE_TYPE_PP = hipe_llvm:mk_pointer(?BYTE_TYPE_P),
%%  I3 = hipe_llvm:mk_load(T2, BYTE_TYPE_PP, T1, [], [], false),
%%  I4 = hipe_llvm:mk_indirectbr(?BYTE_TYPE_P, T2, TypedJumpLabels),
%%  LMap = [{label, L} || L <- Labels],
%%  %% Update data with the info for the jump table
%%  {NewData, JTabLab} =
%%    case hipe_rtl:switch_sort_order(I) of
%%      [] ->
%%        hipe_consttab:insert_block(Data, word, LMap);
%%      SortOrder ->
%%        hipe_consttab:insert_sorted_block(Data, word, LMap, SortOrder)
%%    end,
%%  Relocs2 = relocs_store(TableName, {switch, {TableType, Labels, NrLabels,
%%                                    SortOrder}, JTabLab}, Relocs),
%%  {[I4, I3, I2, I1], Relocs2, NewData}.
%%
%%%%------------------------------------------------------------------------------
%%%% @doc Pass on RTL code in order to fix invoke and closure calls.
%%%% @end
%%%%------------------------------------------------------------------------------
fix_code(Code, Params) ->
  change_calls_signature(Code, Params).

change_calls_signature(Code, Params) ->
  Precoloured = find_precoloured_registers(),
  erlang:display(Precoloured),
  Params1 = Precoloured++Params,
  Code1 = [do_change_call_signature(I, Precoloured) || I <- Code],
  {Code1, Params1}.

do_change_call_signature(I, Precoloured) ->
  case I of
    #call{} ->
      ArgList = hipe_rtl:call_arglist(I),
      DstList = hipe_rtl:call_dstlist(I),
      I1 = hipe_rtl:call_arglist_update(I, Precoloured++ArgList),
      hipe_rtl:call_dstlist_update(I1, Precoloured++DstList);
    #enter{} ->
      ArgList = hipe_rtl:enter_arglist(I),
      I1 = hipe_rtl:enter_arglist_update(I, Precoloured++ArgList),
      hipe_rtl:enter_dstlist_update(I1, Precoloured);
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
%%  SpAdj = find_sp_adj(hipe_rtl:call_arglist(I)),

%%find_sp_adj(ArgList) ->
%%  NrArgs = length(ArgList),
%%  RegArgs = ?NR_ARG_REGS,
%%  case NrArgs > RegArgs of
%%    true ->
%%      (NrArgs-RegArgs)*(?WORD_WIDTH div 8);
%%    false ->
%%      0
%%  end.
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
%%%%------------------------------------------------------------------------------
%%%% Miscellaneous Functions
%%%%------------------------------------------------------------------------------
%%
%%%% @doc Convert RTL argument list to LLVM argument list
%%trans_args(ArgList) ->
%%  Fun1 =
%%    fun(A) ->
%%        {Name, I1} = trans_src(A),
%%        {{?WORD_TYPE, Name}, I1}
%%    end,
%%  lists:map(Fun1,  ArgList).
%%
%%%% @doc Convert a list of Precoloured registers to LLVM argument list
%%fix_reg_args(ArgList) ->
%%  lists:map(fun(A) -> {?WORD_TYPE, A} end, ArgList).
%%
%%%% @doc Load Precoloured registers.
%%load_fixed_regs(RegList) ->
%%  Names = lists:map(fun mk_temp_reg/1, RegList),
%%  Fun1 =
%%    fun (X,Y) ->
%%        hipe_llvm:mk_load(X, ?WORD_TYPE_P, "%"++Y++"_reg_var", [],
%%                          [], false)
%%    end,
%%  Ins = lists:zipwith(Fun1, Names, RegList),
%%  {Names, Ins}.
%%
%%%% @doc  Store Precoloured registers.
%%store_fixed_regs(RegList, Name) ->
%%  Type = ?FUN_RETURN_TYPE,
%%  Names = lists:map(fun mk_temp_reg/1, RegList),
%%  Indexes = lists:seq(0, erlang:length(RegList)-1),
%%  Fun1 =
%%    fun(X,Y) ->
%%        hipe_llvm:mk_extractvalue(X, Type, Name, integer_to_list(Y), [])
%%    end,
%%  I1 = lists:zipwith(Fun1, Names, Indexes),
%%  Fun2 =
%%    fun (X,Y) ->
%%      hipe_llvm:mk_store(?WORD_TYPE, X, ?WORD_TYPE_P, "%"++Y++"_reg_var", [],
%%                          [], false)
%%    end,
%%  I2 = lists:zipwith(Fun2, Names, RegList),
%%  [I2, I1].
%%
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

%%
%%mk_jump_label(N) ->
%%  "%L" ++ integer_to_list(N).
%%
%%mk_temp() ->
%%  "%t" ++ integer_to_list(hipe_gensym:new_var(llvm)).
%%
%%mk_temp_reg(Name) ->
%%  "%"++Name++integer_to_list(hipe_gensym:new_var(llvm)).
%%
%%%%----------------------------------------------------------------------------
%%%%------------------- Translation of Operands ---------------------------------
%%%%----------------------------------------------------------------------------
%%store_stack_dst(TempDst, Dst) ->
%%  {Dst2, II1} = trans_dst(Dst),
%%  II2 = hipe_llvm:mk_store(?WORD_TYPE, TempDst, ?WORD_TYPE_P, Dst2, [], [],
%%                           false),
%%  [II2, II1].
%%
%%store_float_stack(TempDst, Dst) ->
%%  {Dst2, II1} = trans_dst(Dst),
%%  II2 = hipe_llvm:mk_store(?FLOAT_TYPE, TempDst, ?FLOAT_TYPE_P, Dst2, [], [],
%%                           false),
%%  [II2, II1].
%%
%%trans_float_src(Src) ->
%%  case hipe_rtl:is_const_label(Src) of
%%    true ->
%%      Name = "@DL"++integer_to_list(hipe_rtl:const_label_label(Src)),
%%      T1 = mk_temp(),
%%      %% XXX: Hard-Coded offset
%%      I1 = hipe_llvm:mk_getelementptr(T1, ?BYTE_TYPE_P, Name, [{?BYTE_TYPE,
%%                                      integer_to_list(?FLOAT_OFFSET)}], false),
%%      T2 = mk_temp(),
%%      I2 = hipe_llvm:mk_conversion(T2, bitcast, ?BYTE_TYPE_P, T1,
%%                                   ?FLOAT_TYPE_P),
%%      T3 = mk_temp(),
%%      I3 = hipe_llvm:mk_load(T3, ?FLOAT_TYPE_P, T2, [], [], false),
%%      {T3, [I3, I2, I1]};
%%    false -> trans_src(Src)
%%  end.
%%

%%% XXX: Make it shorter
store_opnd(ValueRef, Ptr, Builder, SymTab) ->
  case hipe_rtl:is_var(Ptr) of
    true ->
      Var = hipe_rtl:var_index(Ptr),
      case symtab_fetch({var, Var}, SymTab) of
        undefined ->
          %% Createa an alloca at the Entry block
          CurrentBBRef = symtab_fetch_bb(SymTab),
          FunRef = symtab_fetch_fun(SymTab),
          EntryBBRef = llevm:'LLVMGetFirstBasicBlock'(FunRef),
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
      end;
    false ->
      case hipe_rtl:is_reg(Ptr) of
        true ->
          case isPrecoloured(Ptr) of
            true ->
              store_register(ValueRef, Ptr, Builder, SymTab);
            false ->
              store_precoloured_register(ValueRef, Ptr, Builder, SymTab)
          end;
        false ->
          case hipe_rtl:is_freg(Ptr) of
              true ->
                FReg = hipe_rtl:freg_index(Ptr),
                case symtab_fetch({freg, FReg}, SymTab) of
                  undefined ->
                    %% Createa an alloca at the Entry block
                    CurrentBBRef = symtab_fetch_bb(SymTab),
                    FunRef = symtab_fetch_fun(SymTab),
                    EntryBBRef = llevm:'LLVMGetFirstBasicBlock'(FunRef),
                    llevm:'LLVMPositionBuilderAtEnd'(Builder, EntryBBRef),
                    FRegName = mkFRegName(FReg),
                    PtrRef = llevm:'LLVMBuildAlloca'(Builder, ?WORD_TYPE, FRegName),
                    SymTab1 = symtab_insert({freg, FReg}, PtrRef, SymTab),
                    llevm:'LLVMPositionBuilderAtEnd'(Builder, CurrentBBRef),
                    %% Store the value
                    llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
                    SymTab1;
                  PtrRef ->
                    llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef),
                    SymTab
                end;
              false ->
                exit({?MODULE, store_opnd, {"bad RTL arg",Ptr}})
            end
        end
    end.

store_register(ValueRef, Ptr, Builder, SymTab) ->
  Reg = hipe_rtl:reg_index(Ptr),
  case symtab_fetch({reg, Reg}, SymTab) of
    undefined ->
      %% Createa an alloca at the Entry block
      CurrentBBRef = symtab_fetch_bb(SymTab),
      FunRef = symtab_fetch_fun(SymTab),
      EntryBBRef = llevm:'LLVMGetFirstBasicBlock'(FunRef),
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
      BaseReg = ?ARCH_REGISTERS:proc_pointer(),
      RegName = ?ARCH_REGISTERS:reg_name(Reg),
      {PtrRef, SymTab1} = load_register(BaseReg, Builder, SymTab),
      PtrRef1 = llevm:'LLVMConstIntToPtr'(PtrRef, ?WORD_TYPE_P),
      %%% XXX: ERROR
      %PtrRef2 = llevm:'LLVMBuildGEP'(Builder, PtrRef1, {Offset div (?WORD_WIDTH div 8)},
                                    % 1, RegName),
      llevm:'LLVMBuildStore'(Builder, ValueRef, PtrRef1),
      SymTab1
  end.


%%% XXX: Make it smaller
load_opnd(Ptr, Builder, SymTab) ->
  io:format("Try to load ~w~n",[Ptr]),
  case hipe_rtl:is_imm(Ptr) of
    true ->
      %% Just create the constant
      Value = hipe_rtl:imm_value(Ptr),
      ValueRef = llevm:'LLVMConstInt'(?WORD_TYPE, Value, true),
      io:format("!!!!!ValueRef is ~w~n",[ValueRef]),
      {ValueRef, SymTab};
    false ->
      case hipe_rtl:is_const_label(Ptr) of
        true ->
          ConstLabel = hipe_rtl:const_label_label(Ptr),
          case symtab_fetch({const_label, ConstLabel}, SymTab) of
            undefined ->
              %% Declare a global constant and convert the pointer to integer
              ModRef = symtab_fetch(modRef, SymTab),
              CLName = mkConstLabelName(ConstLabel),
              PtrRef = llevm:'LLVMAddGlobal'(ModRef, ?BYTE_TYPE, CLName),
              llevm:'LLVMSetGlobalConstant'(PtrRef, true),
              ValueRef = llevm:'LLVMConstPtrToInt'(PtrRef, ?WORD_TYPE),
              SymTab1 = symtab_insert({const_label, ConstLabel}, ValueRef, SymTab),
              {ValueRef, SymTab1};
            ValueRef ->
              {ValueRef, SymTab}
          end;
        false ->
          case hipe_rtl:is_var(Ptr) of
            true ->
              Var = hipe_rtl:var_index(Ptr),
              case symtab_fetch({var, Var}, SymTab) of
                undefined ->
                  erlang:display(error_uninitialized_var);
                ValueRef ->
                  %% Load the variable
                  VarName = mkVarName(Var),
                  ValueRef1 = llevm:'LLVMBuildLoad'(Builder, ValueRef, VarName),
                  {ValueRef1, SymTab}
              end;
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
                  case hipe_rtl:is_freg(Ptr) of
                    true ->
                      FReg = hipe_rtl:freg_index(Ptr),
                      case symtab_fetch({freg, FReg}, SymTab) of
                        undefined ->
                          erlang:display(error_uninitialized_var);
                        PtrRef ->
                          %% Load the variable
                          FRegName = mkFRegName(FReg),
                          ValueRef = llevm:'LLVMBuildLoad'(Builder, PtrRef, FRegName),
                          {ValueRef, SymTab}
                      end;
                    false ->
                      exit({?MODULE, trans_dst, {"bad RTL arg",Ptr}})
                  end
              end
          end
      end
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
  io:format("Loading Precoloured ~w~n", [Ptr]),
  Reg = hipe_rtl:reg_index(Ptr),
  case ?ARCH_REGISTERS:proc_offset(Reg) of
    false ->
      load_register(Ptr, Builder, SymTab);
    Offset ->
      BaseReg = hipe_rtl:mk_reg((?ARCH_REGISTERS:proc_pointer())),
      RegName = ?ARCH_REGISTERS:reg_name(Reg),
      {PtrRef, SymTab1} = load_register(BaseReg, Builder, SymTab),
      io:format("loaded base reg~n"),
      PtrRef1 = llevm:'LLVMConstIntToPtr'(PtrRef, ?WORD_TYPE_P),
                         io:format("auto1"),
                         %%%XXX: ERROR
      %PtrRef2 = llevm:'LLVMBuildGEP'(Builder, PtrRef1, {Offset div (?WORD_WIDTH div 8)},
      %                     "fcalls"),
                         io:format("auto"),
      ValueRef = llevm:'LLVMBuildLoad'(Builder, PtrRef1, RegName),
      {ValueRef, SymTab1}
  end.

isPrecoloured(X) -> hipe_rtl_arch:is_precoloured(X).

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

%%trans_fp_op(Op) ->
%%  case Op of
%%    fadd -> fadd;
%%    fsub -> fsub;
%%    fdiv -> fdiv;
%%    fmul -> fmul;
%%    fchs -> fsub;
%%    Other -> exit({?MODULE, trans_fp_op, {"Unknown RTL float Operator",Other}})
%%  end.
%%
%%%% Misc
%%insn_dst(I) ->
%%  case I of
%%    #alu{} -> [hipe_rtl:alu_dst(I)];
%%    #alub{} -> [hipe_rtl:alub_dst(I)];
%%    #call{} ->
%%      case hipe_rtl:call_dstlist(I) of
%%        [] -> [];
%%        [Dst] -> [Dst]
%%      end;
%%    #load{} -> [hipe_rtl:load_dst(I)];
%%    #load_address{} -> [hipe_rtl:load_address_dst(I)];
%%    #load_atom{} -> [hipe_rtl:load_atom_dst(I)];
%%    #move{} -> [hipe_rtl:move_dst(I)];
%%    #phi{} -> [hipe_rtl:phi_dst(I)];
%%    #fconv{} -> [hipe_rtl:fconv_dst(I)];
%%    #fload{} -> [hipe_rtl:fload_dst(I)];
%%    #fmove{} -> [hipe_rtl:fmove_dst(I)];
%%    #fp{} -> [hipe_rtl:fp_dst(I)];
%%    #fp_unop{} -> [hipe_rtl:fp_unop_dst(I)];
%%   _ -> []
%%end.
%%
type_from_size(Size) ->
 case Size of
   byte -> llevm:'LLVMInt1Type'();
   int16 -> llevm:'LLVMInt16Type'();
   int32 -> llevm:'LLVMInt32Type'();
   word -> ?WORD_TYPE
 end.

%% TODO:
%%%%-----------------------------------------------------------------------------
%%%% @doc Create definition for the compiled function. The parameters that are
%%%% passed to the stack must be reversed to much with the CC. Also precoloured
%%%% registers that are passed as arguments must be stored to the corresonding
%%%% stack slots.
%%%%-----------------------------------------------------------------------------
%%create_function_definition(Fun, Params, Code, LocalVars) ->
%%  FunctionName = trans_mfa_name(Fun),
%%  FixedRegs = fixed_registers(),
%%  %% Reverse Parameters to match with the Erlang calling convention
%%  ReversedParams = case erlang:length(Params) > ?NR_ARG_REGS of
%%    false -> Params;
%%    true ->
%%      {ParamsInRegs, ParamsInStack} = lists:split(?NR_ARG_REGS, Params),
%%      ParamsInRegs++lists:reverse(ParamsInStack)
%%  end,
%%  Args = header_regs(FixedRegs) ++ header_params(ReversedParams),
%%  EntryLabel = hipe_llvm:mk_label("Entry"),
%%  Exception_Sync = hipe_llvm:mk_alloca("%exception_sync", ?FLOAT_TYPE, [], []),
%%  I3 = hipe_llvm:mk_br(mk_jump_label(get(first_label))),

%%%%------------------------------------------------------------------------------
%%%%------------------ Specific Stuff for Relocations-----------------------------
%%%%------------------------------------------------------------------------------

%%%% @doc This function is responsible for the actions needed to handle relocations.
%%%% 1) Updates relocations with constants and switch jump tables
%%%% 2) Creates LLVM code to declare relocations as external functions/constants
%%%% 3) Creates LLVM code in order to create local variables for the external
%%%%    constants/labels
%%handle_relocations(Relocs, Data, Fun) ->
%%  RelocsList = relocs_to_list(Relocs),
%%  %% Seperate Relocations according to their type
%%  {CallList, AtomList, ClosureList, ClosureLabels, SwitchList} =
%%    seperate_relocs(RelocsList),
%%  %% Create code to declare atoms
%%  AtomDecl = lists:map(fun declare_atom/1, AtomList),
%%  %% Create code to create local name for atoms
%%  AtomLoad = lists:map(fun load_atom/1, AtomList),
%%  %% Create code to declare closures
%%  ClosureDecl = lists:map(fun declare_closure/1, ClosureList),
%%  %% Create code to create local name for closures
%%  ClosureLoad = lists:map(fun load_closure/1, ClosureList),
%%  %% Find function calls
%%  IsExternalCall = fun (X) -> is_external_call(X, Fun) end,
%%  ExternalCallList = lists:filter(IsExternalCall, CallList),
%%  %% Create code to declare external function
%%  FunDecl = fixed_fun_decl()++lists:map(fun call_to_decl/1, ExternalCallList),
%%  %% Extract constant labels from Constant Map (remove duplicates)
%%  ConstLabels = hipe_consttab:labels(Data),
%%  %% Create code to declare constants
%%  ConstDecl = lists:map(fun declare_constant/1, ConstLabels),
%%  %% Create code to create local name for constants
%%  ConstLoad = lists:map(fun load_constant/1, ConstLabels),
%%  %% Create code to create jump tables
%%  SwitchDecl = declare_switches(SwitchList, Fun),
%%  %% Create code to create a table with the labels of all closure calls
%%  {ClosureLabelDecl, Relocs1} = declare_closure_labels(ClosureLabels, Relocs, Fun),
%%  %% Enter constants to relocations
%%  Relocs2 = lists:foldl(fun const_to_dict/2, Relocs1, ConstLabels),
%%  %% Temporary Store inc_stack and llvm_fix_pinned_regs to Dictionary
%%  %% TODO: Remove this
%%  Relocs3 = dict:store("inc_stack_0",
%%                      {call, {bif, inc_stack_0, 0}}, Relocs2),
%%  Relocs4 = dict:store("hipe_bifs.llvm_fix_pinned_regs.0",
%%                      {call, {hipe_bifs, llvm_fix_pinned_regs, 0}}, Relocs3),
%%  ExternalDeclarations =
%%    AtomDecl++ClosureDecl++ConstDecl++FunDecl++ClosureLabelDecl++SwitchDecl,
%%  LocalVariables = AtomLoad++ClosureLoad++ConstLoad,
%%  {Relocs4, ExternalDeclarations, LocalVariables}.
%%
%%%% @doc Seperate Relocations according to their type
%%seperate_relocs(Relocs) -> seperate_relocs(Relocs, [], [], [], [], []).
%%
%%seperate_relocs([], CallAcc, AtomAcc, ClosureAcc, LabelAcc, JmpTableAcc) ->
%%  {CallAcc, AtomAcc, ClosureAcc, LabelAcc, JmpTableAcc};
%%seperate_relocs([R|Rs], CallAcc, AtomAcc, ClosureAcc, LabelAcc, JmpTableAcc) ->
%%  case R of
%%    {_,{call,_}} ->
%%      seperate_relocs(Rs, [R|CallAcc], AtomAcc, ClosureAcc, LabelAcc,
%%                      JmpTableAcc);
%%    {_,{atom,_}} ->
%%      seperate_relocs(Rs, CallAcc, [R|AtomAcc], ClosureAcc, LabelAcc,
%%                      JmpTableAcc);
%%    {_,{closure,_}} ->
%%      seperate_relocs(Rs, CallAcc, AtomAcc, [R|ClosureAcc], LabelAcc,
%%                      JmpTableAcc);
%%    {_,{switch,_, _}} ->
%%      seperate_relocs(Rs, CallAcc, AtomAcc, ClosureAcc, LabelAcc,
%%                      [R|JmpTableAcc]);
%%    {_,{closure_label,_, _}} ->
%%      seperate_relocs(Rs, CallAcc, AtomAcc, ClosureAcc, [R|LabelAcc],
%%                      JmpTableAcc)
%%  end.
%%

%%%% @doc Declaration of a local variable for a switch jump table
%%declare_switches(JumpTableList, Fun) ->
%%  FunName = trans_mfa_name(Fun),
%%  Fun1 = fun(X) -> declare_switch_table(X, FunName) end,
%%  lists:map(Fun1, JumpTableList).
%%
%%declare_switch_table({Name, {switch, {TableType, Labels, _, _}, _}}, FunName) ->
%%  LabelList = lists:map(fun mk_jump_label/1, Labels),
%%  Fun1 =
%%    fun(X) ->
%%        "i8* blockaddress(@"++FunName++", "++X++")"
%%    end,
%%  List2 = lists:map(Fun1, LabelList),
%%  List3 = string:join(List2, ",\n"),
%%  List4 = "[\n" ++ List3 ++ "\n]\n",
%%  hipe_llvm:mk_const_decl("@"++Name, "constant", TableType, List4).
%%
%%%% @doc Declaration of a variable for a table with the labels of all closure
%%%% calls in the code
%%declare_closure_labels([], Relocs, _Fun) ->
%%  {[], Relocs};
%%declare_closure_labels(ClosureLabels, Relocs, Fun) ->
%%  FunName = trans_mfa_name(Fun),
%%  {LabelList, ArityList} = lists:unzip(
%%                             [{mk_jump_label(Label), A} ||
%%                               {_, {closure_label, Label, A}} <- ClosureLabels]
%%                           ),
%%  Relocs1 = relocs_store("table_closures", {table_closures, ArityList}, Relocs),
%%  Fun1 =
%%    fun(X) ->
%%        "i8* blockaddress(@"++FunName++", "++X++")"
%%    end,
%%  List2 = lists:map(Fun1, LabelList),
%%  List3 = string:join(List2, ",\n"),
%%  List4 = "[\n" ++ List3 ++ "\n]\n",
%%  NrLabels = length(LabelList),
%%  TableType = hipe_llvm:mk_array(NrLabels, ?BYTE_TYPE_P),
%%  {[hipe_llvm:mk_const_decl("@"++"table_closures", "constant", TableType,
%%      List4)], Relocs1}.

%%%% @doc Store external constants and calls to dictionary
%%const_to_dict(Elem, Dict) ->
%%  Name = "DL"++integer_to_list(Elem),
%%  dict:store(Name, {'constant', Elem}, Dict).
%%

%%
%% Misc Functions
%%

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
    FunRef -> FunRef
  end.

symtab_fetch_mod(SymTab) ->
  case symtab_fetch(modRef, SymTab) of
    undefined -> exit({error, symtab_fetch_mod, no_mod_in_symtab});
    ModRef -> ModRef
  end.

relocs_init() -> dict:new().

relocs_store(Key, Value, Relocs) ->
    dict:store(Key, Value, Relocs).

dict_fetch(Key, dict) ->
  try dict:fetch(Key, dict)
  catch
    _:_ -> undefined
  end.
