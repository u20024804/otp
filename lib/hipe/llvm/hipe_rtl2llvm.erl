%% -*- erlang-indent-level: 2 -*-

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").
-include("hipe_llvm.hrl").
-include("../rtl/hipe_literals.hrl").
-export([translate/2, fix_mfa_name/1]).

%% -ifdef(AMD64_FCALLS_IN_REGISTER).
%% -define(FCALLS, "fcalls").
%% -else.
%% -define(FCALLS, "undef").
%% -endif.

%% -ifdef(AMD64_HEAP_LIMIT_IN_REGISTER).
%% -define(HEAP_LIMIT, "heap_limit").
%% -else.
%% -define(HEAP_LIMIT, "undef").
%% -endif.

-define(HIPE_AMD64, true).

-ifdef(HIPE_AMD64).
-define(HIPE_X86_REGISTERS, hipe_amd64_registers).
-define(WORD_TYPE, #llvm_int{width=64}).
-else.
-define(HIPE_X86_REGISTERS, hipe_x86_registers).
-define(WORD_TYPE, #llvm_int{width=32}).
-endif.
%-define(HIPE_X86_REGISTERS, hipe_amd64_registers).
%-define(WORD_TYPE, #llvm_int{width=64}).
-define(WORD_TYPE_P, #llvm_pointer{type=?WORD_TYPE}).

-define(FLOAT_TYPE, #llvm_double{}).
-define(FLOAT_TYPE_P, #llvm_pointer{type=?FLOAT_TYPE}).
-define(BYTE_TYPE, #llvm_int{width=8}).
-define(BYTE_TYPE_P, #llvm_pointer{type=?BYTE_TYPE}).
-define(FUN_RETURN_TYPE,
  #llvm_struct{type_list=[?WORD_TYPE, ?WORD_TYPE, ?WORD_TYPE]}).
-define(NR_PINNED_REGS, 2).


translate(RTL, Roots) ->
  Data = hipe_rtl:rtl_data(RTL),
  Code = hipe_rtl:rtl_code(RTL),
  Fun =  hipe_rtl:rtl_fun(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  {_, MaxLabel} = hipe_rtl:rtl_label_range(RTL),
  {_Mod_Name, Fun_Name, _Arity} = fix_mfa_name(Fun),
  %% Init Unique Symbol Generator
  hipe_gensym:init(llvm),
  put({llvm,label_count}, MaxLabel+1),
  %% Put first label of RTL code in process dictionary
  find_code_entry_label(Code),
  %% Print RTL to file
  {ok, File_rtl} = file:open(atom_to_list(Fun_Name) ++ ".rtl", [write]),
  hipe_rtl:pp(File_rtl, RTL),
  file:close(File_rtl),
  %% Create NewData which containts also data for switches
  {NewData, SwitchValues} = data_from_switches(Code, Data, []),
  %% Create constant map
  {ConstAlign, ConstSize, ConstMap, _RefsFromConsts} =
    hipe_pack_constants:pack_constants([{Fun, [], NewData}],
                                      ?HIPE_X86_REGISTERS:alignment()),
  SC = hipe_pack_constants:llvm_slim_constmap(ConstMap),
  AllocaStack = alloca_stack(Code, Params, Roots),
  {Code2, FailLabels} = fix_code(Code),
  Relocs0 = dict:new(),
  {LLVM_Code1, Relocs1} = translate_instr_list(Code2, [], Relocs0),
  {FinalRelocs, ExternalDecl, LocalVars, TempLabelMap} =
    handle_relocations(Relocs1, SC, SwitchValues, Fun),
  LLVM_Code2 = add_landingpads(LLVM_Code1, FailLabels),
  %% Create LLVM Code for the compiled function
  LLVM_Code3 = create_function_definition(Fun, Params, LLVM_Code2,
                                          AllocaStack++LocalVars),
  %% Final Code = CompiledFunction + External Declarations
  FinalLLVMCode = [LLVM_Code3 | ExternalDecl],
  {FinalLLVMCode, FinalRelocs, SC, ConstAlign, ConstSize, TempLabelMap}.

%%-----------------------------------------------------------------------------
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

%% Create a stack slot for each virtual register. The stack slots
%% that correspond to possible garbage collection roots must be
%% marked as such.
alloca_stack(Code, Params, Roots) ->
  %% Find all assigned virtual registers
  Destinations = collect_destinations(Code),
  %% Declare virtual and registers, and declare garbage collection roots
  alloca_dsts(Destinations++Params, Roots).

collect_destinations(Code) ->
  lists:usort(lists:flatmap(fun insn_dst/1, Code)).

alloca_dsts(Destinations, Roots) -> alloca_dsts(Destinations, Roots, []).
alloca_dsts([], _, Acc) -> Acc;
alloca_dsts([D|Ds], Roots, Acc) ->
  {Name, _I} = trans_dst(D),
  case hipe_rtl:is_var(D) of
    true ->
      Num = hipe_rtl:var_index(D),
      I1 = hipe_llvm:mk_alloca(Name, ?WORD_TYPE, [], []),
      case lists:member(Num, Roots) of
        true ->
          T1 = mk_temp(),
          BYTE_TYPE_PP = hipe_llvm:mk_pointer(?BYTE_TYPE_P),
          I2 = hipe_llvm:mk_conversion(T1, bitcast, ?WORD_TYPE_P, Name,
            BYTE_TYPE_PP),
          I3 = hipe_llvm:mk_call([], false, [], [], #llvm_void{}, "@llvm.gcroot",
            [{BYTE_TYPE_PP, T1}, {?BYTE_TYPE_P, "@gc_metadata"}], []),
          I4 = hipe_llvm:mk_store(?WORD_TYPE, "-5", ?WORD_TYPE_P, Name, [], [],
            false),
          alloca_dsts(Ds, Roots, [I1, I2, I3, I4 | Acc]);
        false ->
          alloca_dsts(Ds, Roots, [I1|Acc])
      end;
    false ->
      case hipe_rtl:is_reg(D) andalso isPrecoloured(D) of
        true -> alloca_dsts(Ds, Roots,  Acc);
        false ->
          case hipe_rtl:is_fpreg(D) of
            true ->
              I1 = hipe_llvm:mk_alloca(Name, ?FLOAT_TYPE, [], []),
              alloca_dsts(Ds, Roots, [I1|Acc]);
            false ->
              I1 = hipe_llvm:mk_alloca(Name, ?WORD_TYPE, [], []),
              alloca_dsts(Ds, Roots, [I1|Acc])
      end
    end
  end.

%%----------------------------------------------------------------------------


%%----------------------------------------------------------------------------
%%----------------------------------------------------------------------------
%%----------------------------------------------------------------------------

translate_instr_list([], Acc, Relocs) ->
  {lists:reverse(lists:flatten(Acc)), Relocs};
translate_instr_list([I|Is], Acc, Relocs) ->
  {Acc1, NewRelocs} = translate_instr(I, Relocs),
  translate_instr_list(Is, [Acc1|Acc], NewRelocs).

translate_instr(I, Relocs) ->
  case I of
    #alu{} -> trans_alu(I, Relocs);
    #alub{} -> trans_alub(I, Relocs);
    #branch{} -> trans_branch(I, Relocs);
    #call{} -> case hipe_rtl:call_fun(I) of
        fwait -> {[], Relocs};
        _ -> trans_call(I, Relocs)
      end;
    #comment{} -> trans_comment(I, Relocs);
    #enter{} -> trans_enter(I, Relocs);
    #fconv{} -> trans_fconv(I, Relocs);
    #fload{} -> trans_fload(I, Relocs);
    #fmove{} -> trans_fmove(I, Relocs);
    #fp{} -> trans_fp(I, Relocs);
    #fp_unop{} -> trans_fp_unop(I, Relocs);
    #fstore{} -> trans_fstore(I, Relocs);
    #goto{} -> trans_goto(I, Relocs);
    #label{} -> trans_label(I, Relocs);
    #load{} -> trans_load(I, Relocs);
    #load_address{} -> trans_load_address(I, Relocs);
    #load_atom{} -> trans_load_atom(I, Relocs);
    #move{} -> trans_move(I, Relocs);
    #return{} -> trans_return(I, Relocs);
    #store{} -> trans_store(I, Relocs);
    #switch{} -> trans_switch(I, Relocs);
    Other ->
      exit({?MODULE, translate_instr, {"unknown RTL instruction", Other}})
  end.

%%-----------------------------------------------------------------------------

%%
%% alu
%%
trans_alu(I, Relocs) ->
  _Dst = hipe_rtl:alu_dst(I),
  _Src1 = hipe_rtl:alu_src1(I),
  _Src2 = hipe_rtl:alu_src2(I),
  {Dst, I1} = trans_stack_dst(_Dst),
  {Src1, I2} = trans_src(_Src1),
  {Src2, I3} = trans_src(_Src2),
  Op =  trans_op(hipe_rtl:alu_op(I)),
  I4 = hipe_llvm:mk_operation(Dst, Op, ?WORD_TYPE, Src1, Src2, []),
  I5 = store_stack_dst(Dst, _Dst),
  {[I5, I4, I3, I2, I1], Relocs}.

%%
%% alub
%%
trans_alub(I, Relocs) ->
  case hipe_rtl:alub_cond(I) of
    overflow ->
      trans_alub_overflow(I, Relocs);
    not_overflow ->
      trans_alub_overflow(I, Relocs);
    _ ->
      trans_alub_no_overflow(I, Relocs)
  end.

trans_alub_overflow(I, Relocs) ->
  %% No Precoloured Registers can exit in an alu with overflow
  {Src1, I1} =  trans_src(hipe_rtl:alub_src1(I)),
  {Src2, I2} =  trans_src(hipe_rtl:alub_src2(I)),
  _Dst = hipe_rtl:alub_dst(I),
  {Dst, I3} = trans_stack_dst(_Dst),
  %% TODO: Fix call
  Name =
  case hipe_rtl:alub_op(I) of
    add -> "llvm.sadd.with.overflow.i64";
    mul -> "llvm.smul.with.overflow.i64";
    sub -> "llvm.ssub.with.overflow.i64";
    Other ->
      exit({?MODULE, trans_alub_overflow, {"Unknown operator in
            alu with overflow", Other}})
  end,
  NewRelocs = relocs_store(Name, {call, {llvm, Name, 2}}, Relocs),
  ReturnType = hipe_llvm:mk_struct([?WORD_TYPE, hipe_llvm:mk_int(1)]),
  T1 = mk_temp(),
  I4 = hipe_llvm:mk_call(T1, false, [], [], ReturnType, "@"++Name,
                        [{?WORD_TYPE, Src1}, {?WORD_TYPE, Src2}], []),
  I5 = hipe_llvm:mk_extractvalue(Dst, ReturnType, T1 , "0", []),
  I6 = store_stack_dst(Dst, _Dst),
  T2 = mk_temp(),
  I7 = hipe_llvm:mk_extractvalue(T2, ReturnType, T1, "1", []),
  case hipe_rtl:alub_cond(I) of
    overflow ->
      True_label = mk_jump_label(hipe_rtl:alub_true_label(I)),
      False_label = mk_jump_label(hipe_rtl:alub_false_label(I));
    not_overflow ->
      True_label = mk_jump_label(hipe_rtl:alub_false_label(I)),
      False_label = mk_jump_label(hipe_rtl:alub_true_label(I))
  end,
  I8 = hipe_llvm:mk_br_cond(T2, True_label, False_label),
  {[I8, I7, I6, I5, I4, I3, I2, I1], NewRelocs}.

trans_alub_no_overflow(I, Relocs) ->
  %% alu
  T = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
                      hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  %% A trans_alu instruction cannot change relocations
  {I1, _} = trans_alu(T, Relocs),
  %% icmp
  _Dst = hipe_rtl:alub_dst(I),
  %% Translate destination as src, to match with the semantic of instruction
  {Dst, I2} = trans_src(_Dst),
  Cond = trans_rel_op(hipe_rtl:alub_cond(I)),
  T3 = mk_temp(),
  I5 = hipe_llvm:mk_icmp(T3, Cond, ?WORD_TYPE, Dst, "0"),
  %% br
  True_label = mk_jump_label(hipe_rtl:alub_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:alub_false_label(I)),
  I6 = hipe_llvm:mk_br_cond(T3, True_label, False_label),
  {[I6, I5, I2, I1], Relocs}.

%%
%% branch
%%
trans_branch(I, Relocs) ->
  %% XXX Can a precoloured register be in an branch instruction ?
  {Src1, I1} = trans_src(hipe_rtl:branch_src1(I)),
  {Src2, I2} = trans_src(hipe_rtl:branch_src2(I)),
  Cond = trans_rel_op(hipe_rtl:branch_cond(I)),
  %% icmp
  T1 = mk_temp(),
  I3 = hipe_llvm:mk_icmp(T1, Cond, ?WORD_TYPE, Src1, Src2),
  %% br
  True_label = mk_jump_label(hipe_rtl:branch_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:branch_false_label(I)),
  I4 = hipe_llvm:mk_br_cond(T1, True_label, False_label),
  {[I4, I3, I2, I1], Relocs}.

%%
%% call
%%
trans_call(I, Relocs) ->
  OriginalName = hipe_rtl:call_fun(I),
  {Dst, I1} =
  case hipe_rtl:call_dstlist(I) of
    [] ->
      {mk_temp(), []};
    [Destination] ->
      trans_stack_dst(Destination)
  end,
  {CallArgs, I0} = trans_call_args(hipe_rtl:call_arglist(I)),
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I2} = load_fixed_regs(FixedRegs),
  FinalArgs =
  case OriginalName of
    {hipe_bifs, llvm_expose_closure, _} ->
      [];
    _ ->
      fix_reg_args(LoadedFixedRegs) ++ CallArgs
  end,
  {Name, I3, NewRelocs} = trans_call_name(OriginalName, Relocs, CallArgs,
                                          FinalArgs),
  T1 = mk_temp(),
  I4 =
  case hipe_rtl:call_fail(I) of
    %% Normal Call
    [] ->
      hipe_llvm:mk_call(T1, false, "cc 11", [], ?FUN_RETURN_TYPE,
                        Name, FinalArgs, []);
    %% Call With Exception
    FailLabelNum ->
      TrueLabel = "L"++integer_to_list(hipe_rtl:call_normal(I)),
     % FailLabel = mk_jump_label(FailLabelNum),
     FailLabel = "%FL"++integer_to_list(FailLabelNum),
      II1 = hipe_llvm:mk_invoke(T1, "cc 11", [], ?FUN_RETURN_TYPE,
        Name, FinalArgs, [], "%"++TrueLabel, FailLabel),
      II2 = hipe_llvm:mk_label(TrueLabel),
      [II2, II1]
  end,
  I5 = store_fixed_regs(FixedRegs, T1),
  I6 =
  case hipe_rtl:call_dstlist(I) of
    [] -> [];
    [Destination2] ->
      II3 = hipe_llvm:mk_extractvalue(Dst, ?FUN_RETURN_TYPE, T1,
        integer_to_list(?NR_PINNED_REGS), []),
      II4 = store_stack_dst(Dst, Destination2),
      [II4, II3]
  end,
  I7 =
  case hipe_rtl:call_continuation(I) of
    [] -> [];
    CC ->
      {II5, _UnusedRelocs} = trans_goto(hipe_rtl:mk_goto(CC), Relocs),
      II5
  end,
  {[I7, I6, I5, I4, I3, I2, I0, I1], NewRelocs}.

%%
%% trans_comment
%%
trans_comment(I, Relocs) ->
  I1 = hipe_llvm:mk_comment(hipe_rtl:comment_text(I)),
  {I1, Relocs}.

%%
%% enter
%%
trans_enter(I, Relocs) ->
  {CallArgs, I0} = trans_call_args(hipe_rtl:enter_arglist(I)),
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_fixed_regs(FixedRegs),
  FinalArgs = fix_reg_args(LoadedFixedRegs) ++ CallArgs,
  {Name, I2, NewRelocs} = trans_call_name(hipe_rtl:enter_fun(I), Relocs,
                                          CallArgs, FinalArgs),
  %% TODO: Fix return type of calls
  T1 = mk_temp(),
  I3 = hipe_llvm:mk_call(T1, true, "cc 11", [], ?FUN_RETURN_TYPE,
                          Name, FinalArgs, []),
  I4 = hipe_llvm:mk_ret([{?FUN_RETURN_TYPE, T1}]),
  {[I4, I3, I2, I1, I0], NewRelocs}.

%%
%% fconv
%%
trans_fconv(I, Relocs) ->
  %% XXX: Can a fconv destination be a precoloured reg?
  _Dst = hipe_rtl:fconv_dst(I),
  {Dst, I1} = trans_stack_dst(_Dst),
  _Src = hipe_rtl:fconv_src(I),
  {Src, I2} =  trans_float_src(_Src),
  I3 = hipe_llvm:mk_conversion(Dst, sitofp, ?WORD_TYPE, Src, ?FLOAT_TYPE),
  I4 = store_float_stack(Dst, _Dst),
  {[I4, I3, I2, I1], Relocs}.


%% TODO: fload, fstore, fmove, and fp are almost the same with load,store,move
%% and alu. Maybe we should join them.

%%
%% fload
%%
trans_fload(I, Relocs) ->
  _Dst = hipe_rtl:fload_dst(I),
  _Src = hipe_rtl:fload_src(I),
  _Offset = hipe_rtl:fload_offset(I),
  {Dst, I1} = trans_stack_dst(_Dst),
  {Src, I2} = trans_float_src(_Src),
  {Offset, I3} = trans_float_src(_Offset),
  T1 = mk_temp(),
  I4 = hipe_llvm:mk_operation(T1, add, ?WORD_TYPE, Src, Offset, []),
  T2 = mk_temp(),
  I5 = hipe_llvm:mk_conversion(T2, inttoptr,  ?WORD_TYPE, T1, ?FLOAT_TYPE_P),
  I6 = hipe_llvm:mk_load(Dst, ?FLOAT_TYPE_P, T2, [], [], false),
  I7 = store_float_stack(Dst, _Dst),
  {[I7, I6, I5, I4, I3, I2, I1], Relocs}.

%%
%% fmove
%%
trans_fmove(I, Relocs) ->
  _Dst = hipe_rtl:fmove_dst(I),
  _Src = hipe_rtl:fmove_src(I),
  %% TODO : Not stack needed?
  {Dst, I1} = trans_stack_dst(_Dst),
  {Src, I2} = trans_float_src(_Src),
  I3 = hipe_llvm:mk_select(Dst, "true", ?FLOAT_TYPE, Src, ?FLOAT_TYPE, "undef"),
  I4 = store_float_stack(Dst, _Dst),
  {[I4, I3, I2, I1], Relocs}.

%%
%% fp
%%
trans_fp(I, Relocs) ->
  %% XXX: Just copied trans_alu...think again..
  _Dst = hipe_rtl:fp_dst(I),
  _Src1 = hipe_rtl:fp_src1(I),
  _Src2 = hipe_rtl:fp_src2(I),
  %% Destination cannot be a precoloured register
  {Dst, I1} = trans_stack_dst(_Dst),
  {Src1, I2} = trans_float_src(_Src1),
  {Src2, I3} = trans_float_src(_Src2),
  Op = trans_fp_op(hipe_rtl:fp_op(I)),
  I4 = hipe_llvm:mk_operation(Dst, Op, ?FLOAT_TYPE, Src1, Src2, []),
  I5 = store_float_stack(Dst, _Dst),
  %% Synchronization for floating point exceptions
  I6 = hipe_llvm:mk_store(?FLOAT_TYPE, Dst, ?FLOAT_TYPE_P, "%exception_sync", [] ,[], true),
  T1 = mk_temp(),
  I7 = hipe_llvm:mk_load(T1, ?FLOAT_TYPE_P, "%exception_sync", [], [] ,true),
  {[I7, I6, I5, I4, I3, I2, I1], Relocs}.

%%
%% fp_unop
%%
trans_fp_unop(I, Relocs) ->
  _Dst = hipe_rtl:fp_unop_dst(I),
  _Src = hipe_rtl:fp_unop_src(I),
  % Destination cannot be a precoloured register
  {Dst, I1} = trans_stack_dst(_Dst),
  {Src, I2} = trans_float_src(_Src),
  Op =  trans_fp_op(hipe_rtl:fp_unop_op(I)),
  I3 = hipe_llvm:mk_operation(Dst, Op, ?FLOAT_TYPE, "0.0", Src, []),
  I4 = store_float_stack(Dst, _Dst),
  {[I4, I3, I2, I1], Relocs}.
%% TODO: Fix fp_unop in a way like the following. You must change trans_dest,
%% in order to call float_to_list in a case of float constant. Maybe the type
%% check is expensive...
% Dst = hipe_rtl:fp_unop_dst(I),
% Src = hipe_rtl:fp_unop_src(I),
% Op = hipe_rtl:fp_unop_op(I),
% Zero = hipe_rtl:mk_imm(0.0),
% I1 = hipe_rtl:mk_fp(Dst, Zero, Op, Src),
% trans_fp(I, Relocs1).

%%
%% fstore
%%
trans_fstore(I, Relocs) ->
  Base = hipe_rtl:fstore_base(I),
  I1 = case isPrecoloured(Base) of
    true -> trans_fstore_reg(I, Relocs);
    false -> exit({?MODULE, trans_fstore ,{"Non Implemened yet", false}})
  end,
  I1.

trans_fstore_reg(I, Relocs) ->
  B = hipe_rtl:fstore_base(I),
  {Base, I0}  = trans_reg(B, dst),
  D1 = mk_hp(),
  I1 = hipe_llvm:mk_load(D1, ?WORD_TYPE_P, Base, [],  [], false),
  D2 = mk_hp(),
  I2 = hipe_llvm:mk_conversion(D2, inttoptr, ?WORD_TYPE, D1, ?FLOAT_TYPE_P),
  {_Offset, I3} = trans_src(hipe_rtl:fstore_offset(I)),
  Offset = integer_to_list(list_to_integer(_Offset) div 8),
  D3 = mk_hp(),
  I4 = hipe_llvm:mk_getelementptr(D3, ?FLOAT_TYPE_P, D2, [{?WORD_TYPE, Offset}],
                                  false),
  _Value = hipe_rtl:fstore_src(I),
  {Value, I5} = trans_src(_Value),
  I6 = hipe_llvm:mk_store(?FLOAT_TYPE, Value, ?FLOAT_TYPE_P, D3, [], [],
                          false),
  {[I6, I5, I4, I3, I2, I1, I0], Relocs}.


%%
%% goto
%%
trans_goto(I, Relocs) ->
  I1 = hipe_llvm:mk_br(mk_jump_label(hipe_rtl:goto_label(I))),
  {I1, Relocs}.

%%
%% label
%%
trans_label(I, Relocs) ->
  Label  = mk_label(hipe_rtl:label_name(I)),
  I1 = hipe_llvm:mk_label(Label),
  {I1, Relocs}.

%%
%% load
%%
trans_load(I, Relocs) ->
  _Dst = hipe_rtl:load_dst(I),
  _Src = hipe_rtl:load_src(I),
  _Offset = hipe_rtl:load_offset(I),
  %%XXX: can destination be a precoloured register????
  {Dst, I1} = trans_stack_dst(_Dst),
  {Src, I2} = trans_src(_Src),
  {Offset, I3} = trans_src(_Offset),
  T1 = mk_temp(),
  I4 = hipe_llvm:mk_operation(T1, add, ?WORD_TYPE, Src, Offset, []),
  Ins = case hipe_rtl:load_size(I) of
    word ->
      T2 = mk_temp(),
      I5 = hipe_llvm:mk_conversion(T2, inttoptr, ?WORD_TYPE, T1, ?WORD_TYPE_P),
      I6 = hipe_llvm:mk_load(Dst, ?WORD_TYPE_P, T2, [], [], false),
      [I6, I5];
    Size ->
      LoadType = type_from_size(Size),
      LoadTypeP = hipe_llvm:mk_pointer(LoadType),
      T2 = mk_temp(),
      I5 = hipe_llvm:mk_conversion(T2, inttoptr, ?WORD_TYPE, T1, LoadTypeP),
      T3 = mk_temp(),
      LoadTypePointer = hipe_llvm:mk_pointer(LoadType),
      I6 = hipe_llvm:mk_load(T3, LoadTypePointer, T2, [], [], false),
      Conversion = case hipe_rtl:load_sign(I) of
        signed -> sext;
        unsigned -> zext
      end,
      I7 = hipe_llvm:mk_conversion(Dst, Conversion, LoadType, T3, ?WORD_TYPE),
      [I7, I6, I5]
  end,
  I8 = store_stack_dst(Dst, _Dst),
  {[I8, Ins, I4, I3, I2, I1], Relocs}.

%%
%% load_address
%%
trans_load_address(I, Relocs) ->
  _Dst = hipe_rtl:load_address_dst(I),
  _Addr = hipe_rtl:load_address_addr(I),
  {Dst, I1} = trans_stack_dst(_Dst),
  {Addr, NewRelocs} =
  case hipe_rtl:load_address_type(I) of
    constant ->
      {"%DL"++integer_to_list(_Addr)++"_var", Relocs};
    closure  ->
      {Closure, _, _} = _Addr,
      {_, ClosureName, _} = Closure,
      FixedClosurename = atom_to_list(fix_closure_name(ClosureName)),
      Relocs1 = relocs_store(FixedClosurename, {closure,_Addr}, Relocs),
      {"%"++FixedClosurename++"_var", Relocs1};
    type ->
      exit({?MODULE,trans_load_address, {"Type not implemented in
          load_address", _Addr}})
  end,
  I2 = hipe_llvm:mk_select(Dst, true, ?WORD_TYPE, Addr, ?WORD_TYPE, "undef"),
  I3 = store_stack_dst(Dst, _Dst),
  {[I3, I2, I1], NewRelocs}.

%%
%% load_atom
%%
trans_load_atom(I, Relocs) ->
  _Dst = hipe_rtl:load_atom_dst(I),
  _Atom = hipe_rtl:load_atom_atom(I),
  {Dst, I1} = trans_stack_dst(_Dst),
  Name = "atom_"++make_llvm_id(atom_to_list(_Atom)),
  Atom_Name = "%"++Name++"_var",
  NewRelocs = relocs_store(Name, {atom, _Atom}, Relocs),
  I2 = hipe_llvm:mk_select(Dst, true, ?WORD_TYPE, Atom_Name, ?WORD_TYPE, "undef"),
  I3 = store_stack_dst(Dst, _Dst),
  {[I3, I2, I1], NewRelocs}.

%%
%% move
%%
trans_move(I, Relocs) ->
  _Dst = hipe_rtl:move_dst(I),
  _Src = hipe_rtl:move_src(I),
  {Dst, I0} = trans_stack_dst(_Dst),
  {Src, I1} = trans_src(_Src),
  I2 = hipe_llvm:mk_select(Dst, "true", ?WORD_TYPE, Src, ?WORD_TYPE, "undef"),
  I3 = store_stack_dst(Dst, _Dst),
  {[I3, I2, I1, I0], Relocs}.

%%
%% return
%%
%% TODO: Take care of returning many items
trans_return(I, Relocs) ->
  {VarRet, I1} =
  case hipe_rtl:return_varlist(I) of
    [] -> {[], []};
    [A] ->
      {Name, II1} = trans_src(A),
      {[{?WORD_TYPE, Name}], II1}
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I2} = load_fixed_regs(FixedRegs),
  FixedRet = lists:map(fun(X) -> {?WORD_TYPE, X} end, LoadedFixedRegs),
  Ret = lists:append(FixedRet, VarRet),
  {RetTypes, _RetNames} = lists:unzip(Ret),
  Type = hipe_llvm:mk_struct(RetTypes),
  {RetStruct, I3} = mk_return_struct(Ret, Type),
  I4 = hipe_llvm:mk_ret([{Type, RetStruct}]),
  {[I4, I3, I2, I1], Relocs}.

mk_return_struct(RetValues, Type) ->
  mk_return_struct(RetValues, Type, [], "undef", 0).

mk_return_struct([], _Type, Acc, StructName, _Index) ->
  {StructName, Acc};
mk_return_struct([{ElemType, ElemName}|Rest], Type, Acc, StructName, Index) ->
  T1 = mk_temp(),
  I1 = hipe_llvm:mk_insertvalue(T1, Type, StructName, ElemType, ElemName,
    integer_to_list(Index), []),
  mk_return_struct(Rest, Type, [I1|Acc], T1, Index+1).

%%
%% store
%%
trans_store(I, Relocs) ->
  {Base, I1} = trans_src(hipe_rtl:store_base(I)),
  {Offset, I2} = trans_src(hipe_rtl:store_offset(I)),
  _Value = hipe_rtl:store_src(I),
  {Value, I3} = trans_src(_Value),
  T1 = mk_temp(),
  I4 = hipe_llvm:mk_operation(T1, add, ?WORD_TYPE, Base, Offset, []),
  I5 =
  case hipe_rtl:store_size(I) of
    word ->
      T2 = mk_temp(),
      II1 = hipe_llvm:mk_conversion(T2, inttoptr, ?WORD_TYPE, T1, ?WORD_TYPE_P),
      II2 = hipe_llvm:mk_store(?WORD_TYPE, Value, ?WORD_TYPE_P, T2, [], [],
                              false),
      [II2, II1];
    Size ->
      %% XXX: Not Tested yet..Is trunc correct ?
      LoadType = type_from_size(Size),
      LoadTypePointer = hipe_llvm:mk_pointer(LoadType),
      T2 = mk_temp(),
      II1 = hipe_llvm:mk_conversion(T2, inttoptr, ?WORD_TYPE, T1, LoadTypePointer),
      T3 = mk_temp(),
      II2 = hipe_llvm:mk_conversion(T3, 'trunc', ?WORD_TYPE, Value, LoadType),
      II3 = hipe_llvm:mk_store(LoadType, T3, LoadTypePointer, T2, [], [], false),
      [II3, II2, II1]
  end,
  {[I5, I4, I3, I2, I1], Relocs}.

%%
%% switch
%%
trans_switch(I, Relocs) ->
  _Src = hipe_rtl:switch_src(I),
  {Src, I1} = trans_src(_Src),
  LabelList = lists:map(fun mk_jump_label/1, hipe_rtl:switch_labels(I)),
  ValueList = lists:map(fun integer_to_list/1, lists:seq(0,
                        length(LabelList)-1)),
  ValueLabelList = lists:zip(ValueList, LabelList),
  I2 = hipe_llvm:mk_switch(?WORD_TYPE, Src, switch_default_label(),
                             ValueLabelList),
  {[I2, I1], Relocs}.

switch_default_label() ->
  FirstLabel =
    case get(first_label) of
      undefined -> exit({?MODULE, switch_default_label, "No first_label in
            process dictionary"});
      Value -> Value
    end,
  "%L"++integer_to_list(FirstLabel).

%%-----------------------------------------------------------------------------

%% Pass on RTL code in order to fix invoke and closure calls.
%% TODO: merge the 2 passes in one.
fix_code(Code) ->
  {Code1, FailLabels} = fix_invoke_calls(Code),
  Code2 = fix_closure_calls(Code1),
  {Code2, FailLabels}.


%% When a call has a fail continuation label it must be extended with a normal
%% continuation label to go with the LLVM's invoke instruction. Also all phi
%% nodes that are correlated with the block that holds tha call instruction
%% must be updated. FailLabels is the list of labels of all fail blocks, which
%% is needed to be declared as landing pads. Also we must go to fail labels
%% and add a call to
%% hipe_bifs:llvm_fix_pinned_regs:0 in order to avoid the reloading of old values of
%% pinned registers(This happens because at fail labels, the result of an
%% invoke instruction is no available, and we cannot get the correct values
%% of pinned registers). Finnaly when there are stack arguments the stack
%% needs to be readjusted.
fix_invoke_calls(Code) -> fix_invoke_calls(Code, [], []).
fix_invoke_calls([], Acc, FailLabels) ->
  {lists:reverse(Acc), FailLabels};

fix_invoke_calls([I|Is], Acc, FailLabels) ->
  case I of
    #call{} ->
      case hipe_rtl:call_fail(I) of
        [] -> fix_invoke_calls(Is, [I|Acc], FailLabels);
        FailLabel ->
          NewLabel = hipe_gensym:new_label(llvm),
          NewCall1 =  hipe_rtl:call_normal_update(I, NewLabel),
          SpAdj = find_sp_adj(hipe_rtl:call_arglist(I)),
          case lists:keyfind(FailLabel, 1, FailLabels) of
            %% Same fail label with same Stack Pointer adjustment
            {FailLabel, NewFailLabel, SpAdj} ->
              NewCall2 = hipe_rtl:call_fail_update(NewCall1, NewFailLabel),
              fix_invoke_calls(Is, [NewCall2|Acc], FailLabels);
            %% Same fail label but with different Stack Pointer adjustment
            {_, _, _} ->
              NewFailLabel = hipe_gensym:new_label(llvm),
              NewCall2 = hipe_rtl:call_fail_update(NewCall1, NewFailLabel),
              fix_invoke_calls(Is, [NewCall2|Acc],
                                [{FailLabel, NewFailLabel, SpAdj}|FailLabels]);
            %% New Fail label
            false ->
              NewFailLabel = hipe_gensym:new_label(llvm),
              NewCall2 = hipe_rtl:call_fail_update(NewCall1, NewFailLabel),
              fix_invoke_calls(Is, [NewCall2|Acc],
                              [{FailLabel, NewFailLabel, SpAdj}|FailLabels])
          end
      end;
    _ -> fix_invoke_calls(Is, [I|Acc], FailLabels)
  end.

find_sp_adj(ArgList) ->
  NrArgs = length(ArgList),
  RegArgs = ?AMD64_NR_ARG_REGS,
  case NrArgs > RegArgs of
    true -> (NrArgs-RegArgs)*8;
    false -> 0
  end.

%% In case of a call to a closure with more than ?AMD64_NR_ARG_REGS, the
%% addresss of the call must be exported in order to fix the corresponding
%% SDesc. This is achieved by introducing a call to
%% hipe_bifs:llvm_expose_closure/0 before the closure call.
fix_closure_calls(Code) ->
  fix_closure_calls(Code, []).

fix_closure_calls([], Acc) ->
  lists:reverse(Acc);
fix_closure_calls([I|Is], Acc) ->
  case I of
    #call{} ->
      Fun = hipe_rtl:call_fun(I),
      case hipe_rtl:is_reg(Fun) of
        true ->
          CallArgs = hipe_rtl:call_arglist(I),
          StackArgs = length(CallArgs)-?AMD64_NR_ARG_REGS,
          case StackArgs > 0 of
            true ->
              NewCall = hipe_rtl:mk_call([], {hipe_bifs, llvm_expose_closure, StackArgs},
                [], [], [], remote),
              fix_closure_calls(Is, [I, NewCall|Acc]);
            false ->
              fix_closure_calls(Is, [I|Acc])
          end;
        false ->
          fix_closure_calls(Is, [I|Acc])
      end;
    _ ->
      fix_closure_calls(Is, [I|Acc])
  end.

%% Add landingpad instruction in Fail Blocks
add_landingpads(LLVM_Code, FailLabels) ->
  FailLabels2 =
    lists:map(fun({X,Y,Z}) ->
          {"L"++integer_to_list(X), "FL"++integer_to_list(Y), Z}
      end, FailLabels),
  add_landingpads(LLVM_Code, FailLabels2, []).

add_landingpads([], _, Acc) ->
  lists:reverse(Acc);
add_landingpads([I|Is], FailLabels, Acc) ->
  case I of
    #llvm_label{} ->
      Label = hipe_llvm:label_label(I),
      Ins = create_fail_blocks(Label, FailLabels),
      add_landingpads(Is, FailLabels, [I|Ins]++Acc);
    _ ->
      add_landingpads(Is, FailLabels, [I|Acc])
  end.

create_fail_blocks(_, []) -> [];
create_fail_blocks(Label, FailLabels) ->
  create_fail_blocks(Label, FailLabels, []).

create_fail_blocks(Label, FailLabels, Acc) ->
  case lists:keytake(Label, 1, FailLabels) of
    false ->
      Acc;
    {value, {Label, FailLabel, SpAdj}, RestFailLabels} ->
      I1 = hipe_llvm:mk_label(FailLabel),
      LP = #llvm_landingpad{},
      I2 = hipe_llvm:mk_adj_stack(integer_to_list(SpAdj)),
      T1 = mk_temp(),
      FixedRegs = fixed_registers(),
      I3 = hipe_llvm:mk_call(T1, false, "cc 11", [], ?FUN_RETURN_TYPE,
        "@hipe_bifs.llvm_fix_pinned_regs.0", [], []),
      I4 = store_fixed_regs(FixedRegs, T1),
      I5 = hipe_llvm:mk_br("%"++Label),
      Ins = [I5|lists:flatten(I4)]++[I3, I2, LP,I1],
      create_fail_blocks(Label, RestFailLabels, Ins++Acc)
  end.

%%----------------------------------------------------------------------------

isPrecoloured(X) -> hipe_rtl_arch:is_precoloured(X).

trans_call_name(Name, Relocs, CallArgs, FinalArgs) ->
  case Name of
    PrimOp when is_atom(PrimOp) ->
      Name1 = trans_prim_op(PrimOp),
      Relocs1  = relocs_store(Name1, {call, {bif, PrimOp,
                                erlang:length(CallArgs)}}, Relocs),
      {"@"++Name1, [], Relocs1};

    {M, F, A} when is_atom(M), is_atom(F), is_integer(A) ->
      Name1 = trans_mfa_name({M,F,A}),
      Relocs1 = relocs_store(Name1, {call, {M,F,A}}, Relocs),
      {"@"++Name1, [], Relocs1};
 		Reg ->
      case hipe_rtl:is_reg(Reg) of
        true ->
          TT1 = mk_temp(),
          {RegName, II1} = trans_src(Reg),
          II2 = hipe_llvm:mk_conversion(TT1, inttoptr, ?WORD_TYPE, RegName,
                                        ?WORD_TYPE_P),
          TT2 = mk_temp(),
          RetType = ?FUN_RETURN_TYPE,
          ArgsTypeList = lists:map(fun (_) -> ?WORD_TYPE end, FinalArgs),
          FunType = hipe_llvm:mk_fun(RetType, ArgsTypeList),
          FunTypeP = hipe_llvm:mk_pointer(FunType),
          II3 = hipe_llvm:mk_conversion(TT2, bitcast, ?WORD_TYPE_P, TT1,
                                        FunTypeP),
          {TT2, [II3, II2, II1], Relocs};
        false ->
          exit({?MODULE, trans_call, {"Unimplemted Call to", Reg}})
      end
  end.

trans_call_args(ArgList) ->
  {Args, I} = lists:unzip(fix_args(ArgList)),
  %% Reverse arguments that are passed to stack to match with the Erlang
  %% calling convention(Propably not needed in prim calls).
  ReversedArgs = case erlang:length(Args) > ?AMD64_NR_ARG_REGS of
    false ->
      Args;
    true ->
      {ArgsInRegs, ArgsInStack} = lists:split(?AMD64_NR_ARG_REGS, Args),
      ArgsInRegs ++ lists:reverse(ArgsInStack)
  end,
  %% Reverse I, because we may kill some of the arguments!! When two or more
  %% arguments they are they same, then order matters!
  {ReversedArgs, lists:reverse(I)}.

% Convert RTL argument list to LLVM argument list
fix_args(ArgList) -> lists:map(fun(A) -> {Name, I1} = trans_src(A),
        {{?WORD_TYPE, Name}, I1} end, ArgList).

% Convert a list of Precoloured registers to LLVM argument list
fix_reg_args(ArgList) -> lists:map(fun(A) -> {?WORD_TYPE, A} end, ArgList).

reg_not_undef(Name) ->
  case Name of
    "undef" -> false;
    _ -> true
  end.

% Load Precoloured registers.
% Names : Tha name of LLVM temp variables
% Ins   : LLVM Instructions that achieve the loading
load_fixed_regs(RegList) ->
  RegList2 = lists:filter(fun reg_not_undef/1, RegList),
  Names = lists:map(fun mk_temp_reg/1, RegList),
  Names2 = lists:filter(fun reg_not_undef/1, Names),
  Ins = lists:zipwith(fun (X,Y) -> hipe_llvm:mk_load(X, ?WORD_TYPE_P, "%"++Y++"_reg_var", [],
                  [], false) end, Names2, RegList2),
  {Names, Ins}.

% Store Precoloured Registers
% Name: The LLVM temp variable name tha holds the struct of return value
store_fixed_regs(RegList, Name) ->
  Type = ?FUN_RETURN_TYPE,
  RegList2 = lists:filter(fun reg_not_undef/1, RegList),
  Names = lists:map(fun mk_temp_reg/1, RegList),
  Indexes = lists:seq(0, erlang:length(RegList2)-1),
  Names2 = lists:filter(fun reg_not_undef/1, Names),
  I1 = lists:zipwith(fun(X,Y) -> hipe_llvm:mk_extractvalue(X, Type, Name,
          integer_to_list(Y), [])
    end, Names2, Indexes),
  I2 = lists:zipwith(fun (X,Y) -> hipe_llvm:mk_store(?WORD_TYPE, X,
          ?WORD_TYPE_P, "%"++Y++"_reg_var", [], [], false) end, Names2,
          RegList2),
  [I2, I1].


make_llvm_id(Name) ->
  case Name of
    "" -> "Empty";
    Other -> lists:flatten(lists:map(fun llvm_id/1, Other))
  end.
llvm_id(C) when C==46; C>47 andalso C<58; C>64 andalso C<91; C==95; C>96 andalso
           C<123 -> C;
llvm_id(C) ->
 io_lib:format("_~2.16.0B_",[C]).
fix_name(Name) ->
  case Name of
    '+' -> unary_plus;
    '++' -> concat;
    Other -> Other
  end.

fix_mfa_name(Fun) ->
  {Mod_Name, Closure_Name, Arity} = Fun,
  Fun_Name = fix_closure_name(Closure_Name),
  {Mod_Name, Fun_Name, Arity}.

fix_closure_name(ClosureName) ->
  CN = atom_to_list(ClosureName),
  list_to_atom(make_llvm_id(CN)).

trans_mfa_name({M,F,A}) ->
  N = atom_to_list(M)++"."++atom_to_list(fix_name(F))++"."++integer_to_list(A),
  make_llvm_id(N).

%%mk_num() -> integer_to_list(hipe_gensym:new_var(llvm)).

mk_label(N) ->
  "L" ++ integer_to_list(N).

mk_jump_label(N) ->
  "%L" ++ integer_to_list(N).

mk_temp() ->
  "%t" ++ integer_to_list(hipe_gensym:new_var(llvm)).
%%mk_temp(N) ->
%%  "%t" ++ integer_to_list(N).

mk_temp_reg(Name) ->
  case reg_not_undef(Name) of
    true -> "%"++Name++integer_to_list(hipe_gensym:new_var(llvm));
    false -> "undef"
  end.

mk_hp() ->
  "%hp_reg_var_" ++ integer_to_list(hipe_gensym:new_var(llvm)).

%% TODO: Remove the use of this function!
trans_stack_dst(_Dst) ->
  {mk_temp(), []}.

store_stack_dst(TempDst, Dst) ->
  {Dst2, II1} = trans_dst(Dst),
  II2 = hipe_llvm:mk_store(?WORD_TYPE, TempDst, ?WORD_TYPE_P, Dst2, [], [], false),
  [II2, II1].

store_float_stack(TempDst, Dst) ->
  {Dst2, II1} = trans_dst(Dst),
  II2 = hipe_llvm:mk_store(?FLOAT_TYPE, TempDst, ?FLOAT_TYPE_P, Dst2, [], [], false),
  [II2, II1].

trans_float_src(Src) ->
  case hipe_rtl:is_const_label(Src) of
    true ->
      Name = "@DL"++integer_to_list(hipe_rtl:const_label_label(Src)),
      T1 = mk_temp(),
      %% XXX: Is offset 6 always valid?
      I1 = hipe_llvm:mk_getelementptr(T1, ?BYTE_TYPE_P, Name, [{?BYTE_TYPE, "6"}], false),
      T2 = mk_temp(),
      I2 = hipe_llvm:mk_conversion(T2, bitcast, ?BYTE_TYPE_P, T1, ?FLOAT_TYPE_P),
      T3 = mk_temp(),
      I3 = hipe_llvm:mk_load(T3, ?FLOAT_TYPE_P, T2, [], [], false),
      {T3, [I3, I2, I1]};
    false -> trans_src(Src)
  end.


%% Translate source and destination arguments
trans_src(A) ->
  case hipe_rtl:is_imm(A) of
    true ->
      Value = integer_to_list(hipe_rtl:imm_value(A)),
      {Value, []};
    false ->
      case hipe_rtl:is_reg(A) of
        true ->
          case isPrecoloured(A) of
            true -> trans_reg(A, src);
            false ->
              {Name, []} = trans_reg(A, src),
              T1 = mk_temp(),
              I1 = hipe_llvm:mk_load(T1, ?WORD_TYPE_P, Name, [], [], false),
              {T1, [I1]}
          end;
        false ->
          case hipe_rtl:is_var(A) of
            true ->
              RootName = "%vr" ++ integer_to_list(hipe_rtl:var_index(A)),
              T1 = mk_temp(),
              I1 = hipe_llvm:mk_load(T1, ?WORD_TYPE_P, RootName, [], [], false),
              I2 =
              case hipe_rtl:var_liveness(A) of
                [] ->
                  [];
                dead ->
                  hipe_llvm:mk_store(?WORD_TYPE, "-5", ?WORD_TYPE_P, RootName, [],
                    [], false)
              end,
              {T1, [I2, I1]};
            false ->
              case hipe_rtl:is_fpreg(A) of
                true ->
                  {Name, []} = trans_dst(A),
                  T1 = mk_temp(),
                  I1 = hipe_llvm:mk_load(T1, ?FLOAT_TYPE_P, Name, [], [], false),
                  {T1, [I1]};
                false -> trans_dst(A)
              end
          end
      end
  end.

trans_dst(A) ->
  case hipe_rtl:is_reg(A) of
    true -> trans_reg(A, dst);
    false ->
      Name = case hipe_rtl:is_var(A) of
        true ->
          "%vr" ++ integer_to_list(hipe_rtl:var_index(A));
        false ->
          case hipe_rtl:is_fpreg(A) of
            true -> "%fr" ++ integer_to_list(hipe_rtl:fpreg_index(A));
            false ->
              case hipe_rtl:is_const_label(A) of
                true ->
                  "%DL"++integer_to_list(hipe_rtl:const_label_label(A))++"_var";
                false ->
                  exit({?MODULE, trans_dst, {"bad RTL arg",A}})
              end
          end
      end,
      {Name, []}
  end.

%% Translate register. If it is precoloured it must be mapped to some llvm var
%% that corresponds to an argument
trans_reg(Arg, Position) ->
  Index = hipe_rtl:reg_index(Arg),
  case isPrecoloured(Arg) of
    true ->
      Name = map_precoloured_reg(Index),
      case Position of
        src -> fix_reg_src(Name);
        dst -> fix_reg_dst(Name)
      end;
    false ->
      {hipe_rtl_arch:reg_name(Index), []}
  end.

map_precoloured_reg(Index) ->
  %TODO : Works only for amd64 architecture and only for register r15
  case hipe_rtl_arch:reg_name(Index) of
    "%r15" -> "%hp_reg_var";
    "%rbp" -> "%p_reg_var";
    "%fcalls" -> {"%p_reg_var", hipe_amd64_registers:proc_offset(hipe_amd64_registers:fcalls())};
    "%hplim" -> {"%p_reg_var", hipe_amd64_registers:proc_offset(hipe_amd64_registers:heap_limit())};
    _ ->  exit({?MODULE, map_precoloured_reg, {"Register not mapped yet",
            Index}})
  end.

fix_reg_dst(Register) ->
  case Register of
    {Name, Offset} ->
      Type = ?WORD_TYPE,
      pointer_from_reg(Name, Type, Offset);
    Name ->
      {Name, []}
  end.

fix_reg_src(Register) ->
  case Register of
    {Name, Offset} ->
      {T1, I1} = pointer_from_reg(Name, ?WORD_TYPE, Offset),
      T2 = mk_temp(),
      I2 = hipe_llvm:mk_load(T2, ?WORD_TYPE_P, T1, [], [] , false),
      {T2, [I2,I1]};
    Name ->
      T1 = mk_temp(),
      {T1, hipe_llvm:mk_load(T1, ?WORD_TYPE_P, Name, [], [], false)}
  end.

pointer_from_reg(RegName, Type, Offset) ->
  PointerType = hipe_llvm:mk_pointer(Type),
  T1 = mk_temp(),
  I1 = hipe_llvm:mk_load(T1, PointerType, RegName, [], [] ,false),
  T2 = mk_temp(),
  I2 = hipe_llvm:mk_conversion(T2, inttoptr, Type, T1, PointerType),
  T3 = mk_temp(),
  %% TODO: FIX offsets!!!
  I3 = hipe_llvm:mk_getelementptr(T3, PointerType, T2, [{Type,
        erlang:integer_to_list(Offset div 8)}], false),
  {T3, [I3, I2, I1]}.


insn_dst(I) ->
  case I of
    #alu{} -> [hipe_rtl:alu_dst(I)];
    #alub{} -> [hipe_rtl:alub_dst(I)];
    #call{} ->
      case hipe_rtl:call_dstlist(I) of
        [] -> [];
        [_, _ |[]] -> exit({?MODULE, insn_dst, {"Call destination list
                not implemented yet", hipe_rtl:call_dstlist(I)}});
                [Dst] -> [Dst]
              end;
    #load{} -> [hipe_rtl:load_dst(I)];
    #load_address{} -> [hipe_rtl:load_address_dst(I)];
    #load_atom{} -> [hipe_rtl:load_atom_dst(I)];
    #move{} -> [hipe_rtl:move_dst(I)];
    #phi{} -> [hipe_rtl:phi_dst(I)];
    #fconv{} -> [hipe_rtl:fconv_dst(I)];
    #fload{} -> [hipe_rtl:fload_dst(I)];
    #fmove{} -> [hipe_rtl:fmove_dst(I)];
    #fp{} -> [hipe_rtl:fp_dst(I)];
    #fp_unop{} -> [hipe_rtl:fp_unop_dst(I)];
   _ -> []
end.

type_from_size(Size) ->
  case Size of
    byte -> #llvm_int{width=8};
    int16 -> #llvm_int{width=16};
    int32 -> #llvm_int{width=32};
    word -> #llvm_int{width=64}
  end.

trans_fp_op(Op) ->
  case Op of
    fadd -> fadd;
    fsub -> fsub;
    fdiv -> fdiv;
    fmul -> fmul;
    fchs -> fsub;
    Other -> exit({?MODULE, trans_fp_op, {"Unknown RTL float Operator",Other}})
  end.

trans_op(Op) ->
  case Op of
    add -> add;
    sub -> sub;
    'or' -> 'or';
    'and' -> 'and';
    'xor' -> 'xor';
    sll -> shl;
    srl -> lshr;
    sra -> ashr;
    mul -> mul;
    'fdiv' -> fdiv;
    'sdiv' -> sdiv;
    'srem' -> srem;
    Other -> exit({?MODULE, trans_op, {"Unknown RTL Operator",Other}})
  end.

trans_rel_op(Op) ->
  case Op of
    eq -> eq;
    ne -> ne;
    gtu -> ugt;
    geu -> uge;
    ltu -> ult;
    leu -> ule;
    gt -> sgt;
    ge -> sge;
    lt -> slt;
    le -> sle
  end.

trans_prim_op(Op) ->
  case Op of
    '+' -> "bif_add";
    '-' -> "bif_sub";
    '*' -> "bif_mul";
    'div' -> "bif_div";
    '/' -> "bif_div";
    Other -> atom_to_list(Other)
  end.

%%-----------------------------------------------------------------------------

%% Create definition for the compiled function

create_function_definition(Fun, Params, Code, LocalVars) ->
  FunctionName = trans_mfa_name(Fun),
  Fixed_regs = fixed_registers(),
  Args1 = header_regs(Fixed_regs),
  %% Reverse Parameters to match with the Erlang calling convention
  ReversedParams = case erlang:length(Params) > ?AMD64_NR_ARG_REGS of
    false -> Params;
    true ->
      {ParamsInRegs, ParamsInStack} = lists:split(?AMD64_NR_ARG_REGS, Params),
      ParamsInRegs++lists:reverse(ParamsInStack)
  end,
  Args2 = lists:map( fun(X) -> {?WORD_TYPE, "%v" ++
          integer_to_list(hipe_rtl:var_index(X))}
    end, ReversedParams),
  I1 = hipe_llvm:mk_label("Entry"),
  Exception_Sync = hipe_llvm:mk_alloca("%exception_sync", ?FLOAT_TYPE, [], []),
  RegList = lists:filter(fun reg_not_undef/1, Fixed_regs),
  I2 = load_regs(RegList),
  %% TODO: Jump to correct label
  [First_Label|_] = Code,
  LLLL = hipe_llvm:label_label(First_Label),
  I3 = hipe_llvm:mk_br("%"++LLLL),
  StoredParams = store_params(Params),
  Final_Code = lists:flatten([I1, Exception_Sync, I2, LocalVars, StoredParams, I3])++Code,
  %% XXX Functions always return something?

  TypeList = lists:map(fun (_) -> ?WORD_TYPE end, Fixed_regs),
  RetType = hipe_llvm:mk_struct([?WORD_TYPE | TypeList]),
  hipe_llvm:mk_fun_def([], [], "cc 11", [], RetType, FunctionName,
                        Args1++Args2,
                        [nounwind, noredzone, list_to_atom("gc \"erlang_gc\"")],
                        [],Final_Code).


store_params(Params) ->
  lists:map(fun(X) ->
        Index = hipe_rtl:var_index(X),
        {Name, _} = trans_dst(X),
        ParamName =  "%v" ++ integer_to_list(Index),
        hipe_llvm:mk_store(?WORD_TYPE, ParamName, ?WORD_TYPE_P, Name,  [],[],false)
    end, Params).

fixed_registers() ->
  case get(hipe_target_arch) of
    x86 -> ["hp", "p"];
    amd64 ->
      ["hp", "p"];
    Other ->
      exit({?MODULE, map_registers, {"Unknown Architecture", Other}})
  end.

header_regs(Regs) -> header_regs(Regs, []).

header_regs([], Acc) -> lists:reverse(Acc);
header_regs([R|Rs], Acc) ->
  case R of
    "undef" ->
      Reg = {?WORD_TYPE,  mk_temp()},
      header_regs(Rs, [Reg|Acc]);
    _ ->
      Reg = {?WORD_TYPE,  "%"++R++"_in"},
      header_regs(Rs, [Reg|Acc])
  end.

load_regs(Regs) -> load_regs(Regs, []).

load_regs([], Acc) -> Acc;
load_regs([R | Rs], Acc) ->
  I1 = hipe_llvm:mk_alloca("%"++R++"_reg_var", ?WORD_TYPE, [], []),
  I2 = hipe_llvm:mk_store(?WORD_TYPE, "%"++R++"_in", ?WORD_TYPE_P, "%"++R++"_reg_var", [], [], false),
  load_regs(Rs, [I1,I2,Acc]).


%%----------------------------------------------------------------------------

relocs_store(Key, Value, Relocs) ->
  dict:store(Key, Value, Relocs).

relocs_to_list(Relocs) ->
  dict:to_list(Relocs).

%%----------------------------------------------------------------------------

%% This function is responsible for the actions needed to handle relocations.
%% 1) Updates relocations with constants and switch jump tables
%% 2) Creates LLVM code to declare relocations as external functions/constants
%% 3) Creates LLVM code in order to create local variables for the external
%%    constants/labels
%% 4) Creates a temporary LabelMap
handle_relocations(Relocs, SlimedConstMap, SwitchValues, Fun) ->
  RelocsList = relocs_to_list(Relocs),
  %% Seperate Relocations according to their type
  {CallList, AtomList, ClosureList} = seperate_relocs(RelocsList),
  %% Create code to declare atoms
  AtomDecl = lists:map(fun declare_atom/1, AtomList),
  %% Create code to create local name for atoms
  AtomLoad = lists:map(fun load_atom/1, AtomList),
  %% Create code to declare closures
  ClosureDecl = lists:map(fun declare_closure/1, ClosureList),
  %% Create code to create local name for closures
  ClosureLoad = lists:map(fun load_closure/1, ClosureList),
  %% Find function calls
  IsExternalCall = fun (X) -> is_external_call(X, Fun) end,
  ExternalCallList = lists:filter(IsExternalCall, CallList),
  %% Create code to declare external function
  FunDecl = fixed_fun_decl()++lists:map(fun call_to_decl/1, ExternalCallList),
  %% Extract constant labels from Constant Map (remove duplicates)
  ConstLabels = lists:usort(find_constants(SlimedConstMap)),
  %% Create code to declare constants
  ConstDecl = lists:map(fun declare_constant/1, ConstLabels),
  %% Create code to create local name for constants
  ConstLoad = lists:map(fun load_constant/1, ConstLabels),
  %% Enter constants to relocations
  Relocs1 = lists:foldl(fun const_to_dict/2, Relocs, ConstLabels),
  %% Temporary Store inc_stack and llvm_fix_pinned_regs to Dictionary
  Relocs2 = dict:store("inc_stack_0", {call, {bif, inc_stack_0, 0}},
                        Relocs1),
  %% TODO: Remove this
  Relocs3 = dict:store("hipe_bifs.llvm_fix_pinned_regs.0", {call, {hipe_bifs,
        llvm_fix_pinned_regs, 0}},
                        Relocs2),
  %% Create LabelMap
  TempLabelMap = lists:map(fun create_label_map/1, SwitchValues),
  %% Store Swich Jump Tables to reloactions
  Relocs4 = labels_to_dict(TempLabelMap, Relocs3),
  ExternalDeclarations = AtomDecl++ClosureDecl++ConstDecl++FunDecl,
  LocalVariables = AtomLoad++ClosureLoad++ConstLoad,
  {Relocs4, ExternalDeclarations, LocalVariables, TempLabelMap}.

%%  Seperate Relocations found in the code to calls, atoms and closures
seperate_relocs(Relocs) -> seperate_relocs(Relocs, [], [], []).

seperate_relocs([], CallAcc, AtomAcc, ClosureAcc) ->
  {CallAcc, AtomAcc, ClosureAcc};
seperate_relocs([R|Rs], CallAcc, AtomAcc, ClosureAcc) ->
  case R of
    {_,{call,_}} -> seperate_relocs(Rs, [R|CallAcc], AtomAcc, ClosureAcc);
    {_,{atom,_}} -> seperate_relocs(Rs, CallAcc, [R|AtomAcc], ClosureAcc);
    {_,{closure,_}} -> seperate_relocs(Rs, CallAcc, AtomAcc, [R|ClosureAcc])
  end.

%% External declaration of an atom
declare_atom({AtomName, _}) ->
  hipe_llvm:mk_const_decl("@"++AtomName, "external constant", ?WORD_TYPE, "").

%% Creation of local variable for an atom
load_atom({AtomName, _}) ->
  Dst = "%"++AtomName++"_var",
  Name = "@"++AtomName,
  hipe_llvm:mk_conversion(Dst, ptrtoint, ?WORD_TYPE_P, Name, ?WORD_TYPE).

%% External declaration of a closure
declare_closure({ClosureName, _})->
  hipe_llvm:mk_const_decl("@"++ClosureName, "external constant", ?BYTE_TYPE, "").

%% Creation of local variable for a closure
load_closure({ClosureName, _})->
  Dst = "%"++ClosureName++"_var",
  Name = "@"++ClosureName,
  hipe_llvm:mk_conversion(Dst, ptrtoint, ?BYTE_TYPE_P, Name, ?WORD_TYPE).

%% A call is treated as non external only in a case of a recursive function
is_external_call({_, {call, Fun}}, Fun) -> false;
is_external_call(_, _) -> true.

%% External declaration of a function
call_to_decl({Name, {call, MFA}}) ->
  {M, F, A} = MFA,
  Cconv = "cc 11",
  {Type, Args} = case M of
    llvm ->
      {hipe_llvm:mk_struct([?WORD_TYPE, hipe_llvm:mk_int(1)]),
        lists:seq(1,2)};
    hipe_bifs ->
      case F of
        llvm_expose_closure -> {?FUN_RETURN_TYPE, []};
        %% +precoloured regs
        _ -> {?FUN_RETURN_TYPE, lists:seq(1,A+?NR_PINNED_REGS)}
      end;
    %% +precoloured regs
    _ -> {?FUN_RETURN_TYPE, lists:seq(1,A+?NR_PINNED_REGS)}
  end,
  ArgsTypes = lists:map(fun(_) -> ?WORD_TYPE end, Args),
  hipe_llvm:mk_fun_decl([], [], Cconv, [], Type, "@"++Name, ArgsTypes, []).

%% This functions are always declared, even if not used
fixed_fun_decl() ->
  LandPad = hipe_llvm:mk_fun_decl([], [], [], [], #llvm_int{width=32},
    "@__gcc_personality_v0", [#llvm_int{width=32}, #llvm_int{width=64},
      ?BYTE_TYPE_P, ?BYTE_TYPE_P], []),
  GCROOTDecl = hipe_llvm:mk_fun_decl([], [], [], [], #llvm_void{},
    "@llvm.gcroot", [hipe_llvm:mk_pointer(?BYTE_TYPE_P), ?BYTE_TYPE_P], []),
  FixPinnedRegs = hipe_llvm:mk_fun_decl([], [], [], [], ?FUN_RETURN_TYPE,
    "@hipe_bifs.llvm_fix_pinned_regs.0", [], []),
  GcMetadata = hipe_llvm:mk_const_decl("@gc_metadata", "external constant",
    ?BYTE_TYPE, ""),
  [LandPad, GCROOTDecl, FixPinnedRegs, GcMetadata].

%% Create NewData which contains blocks for JumpTables. Also
%% return necessary information to create LabelMap
data_from_switches([], NewData, SortedBy) -> {NewData, lists:reverse(SortedBy)};
data_from_switches([I|Is], Data, Sorted) ->
  case I of
    #switch{} ->
      Labels = hipe_rtl:switch_labels(I),
      LMap = [{label,L} || L <- Labels],
      {NewData, JTabLab} =
      case hipe_rtl:switch_sort_order(I) of
        [] ->
          hipe_consttab:insert_block(Data, word, LMap);
        SortOrder ->
          hipe_consttab:insert_sorted_block(
            Data, word, LMap, SortOrder)
      end,
      data_from_switches(Is, NewData, [{JTabLab, length(Labels),hipe_rtl:switch_sort_order(I)}|Sorted]);
    _ -> data_from_switches(Is, Data, Sorted)
  end.

create_label_map([]) -> [];
create_label_map({_,_, []}=LM) -> LM;
create_label_map({ConstNumber, _, SortOrder}) -> {ConstNumber, sorted,
    length(SortOrder)*8,SortOrder}.

labels_to_dict(TempLabelMap, Dict) ->
  labels_to_dict(TempLabelMap, Dict, 0).

labels_to_dict([], Dict,_) -> Dict;
labels_to_dict([{ConstNumber, _, []}|Rest], Dict, RodataNumber) ->
  Dict1 = dict:store(".rodata"++integer_to_list(RodataNumber), {constant,
      ConstNumber}, Dict),
  labels_to_dict(Rest, Dict1, RodataNumber+1);
labels_to_dict([{ConstNumber, _, _, _}|Rest], Dict, RodataNumber) ->
  Dict1 = dict:store(".rodata"++integer_to_list(RodataNumber), {constant,
      ConstNumber}, Dict),
  labels_to_dict(Rest, Dict1, RodataNumber+1).



%% Extract Type of Constants from ConstMap
find_constants(ConstMap) -> find_constants(ConstMap, []).
find_constants([], LabelAcc) -> LabelAcc;
find_constants([Label, _, _, _| Rest], LabelAcc) ->
  find_constants(Rest, [Label| LabelAcc]).

%% Declare an External Consant. We declare all constants as i8
%% in order to be able to calcucate pointers of the form DL+6, with
%% the getelementptr instruction. Otherwise we have to convert constants form
%% pointers to values, add the offset and convert them again to pointers
declare_constant(Label) ->
  Name = "@DL"++integer_to_list(Label),
  hipe_llvm:mk_const_decl(Name, "external constant", ?BYTE_TYPE, "").

%% Loading of a constant depends on it's type. Float constants are loaded
%% to double (with offset 6?), and all other constants are converted from
%% pointers to 64 integers.
load_constant(Label) ->
  Dst = "%DL"++integer_to_list(Label)++"_var",
  Name = "@DL"++integer_to_list(Label),
  hipe_llvm:mk_conversion(Dst, ptrtoint, ?BYTE_TYPE_P, Name, ?WORD_TYPE).


%% Store external constants and calls to dictionary
const_to_dict(Elem, Dict) ->
  Name = "DL"++integer_to_list(Elem),
  dict:store(Name, {'constant', Elem}, Dict).
