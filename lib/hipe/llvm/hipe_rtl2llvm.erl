%% -*- erlang-indent-level: 2 -*-

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").
-include("hipe_llvm.hrl").
-include("../rtl/hipe_literals.hrl").
-export([translate/1, fix_mfa_name/1]).

-define(HP, "hp").
-define(P, "p").
-define(NSP, "nsp").

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

-define(HIPE_X86_REGISTERS, hipe_amd64_registers).


translate(RTL) ->
  hipe_gensym:init(llvm),
  Data = hipe_rtl:rtl_data(RTL),
  Code = hipe_rtl:rtl_code(RTL),
  Fun =  hipe_rtl:rtl_fun(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  {_Mod_Name, Fun_Name, _Arity} = fix_mfa_name(Fun),
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
  %% Collect gc roots
  %% GCRoots = collect_gc_roots(Code),
  %% GCRootDeclare = declare_gc_roots(GCRoots),
  Code2 = fix_invoke_calls(Code),
  Relocs0 = dict:new(),
  {LLVM_Code, Relocs1} = translate_instr_list(Code2, [], Relocs0),
  {FinalRelocs, ExternalDecl, LocalVars, TempLabelMap} = 
    handle_relocations(Relocs1, SC, SwitchValues, Fun),
  %% Create LLVM Code for the compiled function
  LLVM_Code2 = create_function_definition(Fun, Params, LLVM_Code, LocalVars),
  %% Final Code = CompiledFunction + External Declarations
  FinalLLVMCode = [LLVM_Code2 | ExternalDecl],
  {FinalLLVMCode, FinalRelocs, SC, ConstAlign, ConstSize, TempLabelMap}.

%%-----------------------------------------------------------------------------


%%collect_gc_roots(Code) -> collect_gc_roots(Code, []).
%%
%%collect_gc_roots([], Roots) -> Roots;
%%collect_gc_roots([I|Is], Roots) ->
%%  Dst = insn_dst(I),
%%  case Dst of 
%%    [] ->  collect_gc_roots(Is, Roots);
%%    _ -> 
%%      case hipe_rtl:is_var(Dst) of
%%        true -> collect_gc_roots(Is, [Dst|Roots]);
%%        false -> collect_gc_roots(Is, Roots)
%%      end
%%  end.
%%
%%declare_gc_roots(Roots) -> declare_gc_roots(Roots, []).
%%
%%declare_gc_roots([], Ins) -> Ins;
%%declare_gc_roots([Root|Rest], Ins) -> 
%%  GCRootName = trans_dst(Root) ++ "_gcroot",
%%  I1 = hipe_llvm:mk_alloca(GCRootName, "i64*", [], []),
%%  T1 = mk_temp(),
%%  I2 = hipe_llvm:mk_conversion(T1, bitcast, "i64**", GCRootName, "i8**"),
%%  I3 = hipe_llvm:mk_call([], false, [], [], void, "@llvm.gcroot", 
%%    [{"i8**",T1}, {"i8*", "null"}], []),
%%  declare_gc_roots(Rest, [I1, I2, I3 | Ins]).

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
        fwait -> io:format("Fwait found~n"),{[], Relocs};
        _ -> trans_call(I, Relocs)
      end;
    #comment{} -> trans_comment(I, Relocs);
    #enter{} -> trans_enter(I, Relocs);
    #fconv{} -> trans_fconv(I, Relocs);
    #fixnumop{} -> trans_fixnum(I, Relocs);
    #fload{} -> trans_fload(I, Relocs);
    #fmove{} -> trans_fmove(I, Relocs);
    #fp{} -> trans_fp(I, Relocs);
    #fp_unop{} -> trans_fp_unop(I, Relocs);
    #fstore{} -> trans_fstore(I, Relocs);
    #gctest{} -> trans_gctest(I, Relocs);
    #goto{} -> trans_goto(I, Relocs);
    %#goto_index{} -> ok;
    #label{} -> trans_label(I, Relocs);
    #load{} -> trans_load(I, Relocs);
    #load_address{} -> trans_load_address(I, Relocs);
    #load_atom{} -> trans_load_atom(I, Relocs);
    %#load_word_index{} -> ok;
    #move{} -> trans_move(I, Relocs);
    %#multimove{} -> ok;
    #phi{} -> trans_phi(I, Relocs);
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
  IsDstColoured = isPrecoloured(_Dst),
  {Dst, I1} = case IsDstColoured of
    true -> {mk_temp(), []};
    false -> trans_dst(_Dst)
  end,
  {Src1, I2} = trans_src(_Src1),
  {Src2, I3} = trans_src(_Src2), 
  Type = "i64",
  Op =  trans_op(hipe_rtl:alu_op(I)),
  I4 = hipe_llvm:mk_operation(Dst, Op, Type, Src1, Src2, []),
  I5 = case IsDstColoured of 
    true -> 
      {Dst2, II1} = trans_dst(_Dst),
      II2 = hipe_llvm:mk_store(Type, Dst, Type, Dst2, [], [], false),
      [II2, II1];
    false -> []
  end,
  {[I5, I4, I3, I2, I1], Relocs}.
          
%%
%% alub
%%
trans_alub(I, Relocs) ->
  case hipe_rtl:alub_cond(I) of
    overflow -> trans_alub_overflow(I, Relocs);
    not_overflow -> trans_alub_overflow(I, Relocs);
    _ -> trans_alub_no_overflow(I, Relocs)
  end.

trans_alub_overflow(I, Relocs) ->
  T1 = mk_temp(),
  %% No Precoloured Registers can exit in an alu with overflow
  {Src1, []} =  trans_src(hipe_rtl:alub_src1(I)),
  {Src2, []} =  trans_src(hipe_rtl:alub_src2(I)),
  %% TODO: Fix call
  Name = case hipe_rtl:alub_op(I) of
          add -> "llvm.sadd.with.overflow.i64";
          mul -> "llvm.smul.with.overflow.i64";
          sub -> "llvm.ssub.with.overflow.i64";
          Other -> exit({?MODULE, trans_alub_overflow, {"Unknown operator in
                  alu with overflow", Other}})
        end,
  NewRelocs = relocs_store(Name, {call, {llvm, "llvm.sadd.with.overflow.i64",
        2}}, Relocs),
  I1 = hipe_llvm:mk_call(T1, false, [], [], "{i64, i1}", "@"++Name,
                        [{"i64", Src1},{"i64", Src2}], []),
  {Dst, []} = trans_dst(hipe_rtl:alub_dst(I)),
  I2 = hipe_llvm:mk_extractvalue(Dst, "{i64, i1}", T1 , "0", []),
  T2 = mk_temp(),
  I3 = hipe_llvm:mk_extractvalue(T2, "{i64, i1}", T1, "1", []),
  case hipe_rtl:alub_cond(I) of
    overflow ->
      True_label = mk_jump_label(hipe_rtl:alub_true_label(I)),
      False_label = mk_jump_label(hipe_rtl:alub_false_label(I));
    not_overflow ->
      True_label = mk_jump_label(hipe_rtl:alub_false_label(I)),
      False_label = mk_jump_label(hipe_rtl:alub_true_label(I))
  end,
  I4 = hipe_llvm:mk_br_cond(T2, True_label, False_label),
  {[I4, I3, I2, I1], NewRelocs}.

trans_alub_no_overflow(I, Relocs) ->
  %%alu
  T = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
    hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  %% a trans_alu instruction cannot change relocations
  {I1, _} = trans_alu(T, Relocs),
  %%icmp
  _Dst = hipe_rtl:alub_dst(I),
  %% Translate destination as src, to match with the semantic of instruction
  {Dst, I2} = trans_src(_Dst),
  %%_Src1 = hipe_rtl:alub_src1(I),
  %%_Src2 = hipe_rtl:alub_src2(I),
  %%{Src1, I3} = trans_src(_Src1),
  %%{Src2, I4} = trans_src(_Src2),
  Type = "i64",
  Cond = trans_rel_op(hipe_rtl:alub_cond(I)),
  T3 = mk_temp(),
  I5 = hipe_llvm:mk_icmp(T3, Cond, Type, Dst, "0"),
  %%br
  True_label = mk_jump_label(hipe_rtl:alub_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:alub_false_label(I)),
  I6 = hipe_llvm:mk_br_cond(T3, True_label, False_label),
  {[I6, I5, I2, I1], Relocs}.

%%
%% branch
%%
trans_branch(I, Relocs) ->
  Type = "i64",
  {Src1, []} = trans_src(hipe_rtl:branch_src1(I)),
  {Src2, []} = trans_src(hipe_rtl:branch_src2(I)),
  Cond = trans_rel_op(hipe_rtl:branch_cond(I)),
  %% icmp
  T1 = mk_temp(),
  I1 = hipe_llvm:mk_icmp(T1, Cond, Type, Src1, Src2),
  %% br
  True_label = mk_jump_label(hipe_rtl:branch_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:branch_false_label(I)),
  I2 = hipe_llvm:mk_br_cond(T1, True_label, False_label),
  {[I2, I1], Relocs}.


%%
%% call
%%
trans_call(I, Relocs) ->
  %% TODO: Fix Destination List
  {Dst, []} =  case hipe_rtl:call_dstlist(I) of
    [] -> {mk_temp(), []};
    [Destination] -> trans_dst(Destination);
    [_D|_Ds] -> exit({?MODULE, trans_prim_call, "Destination list not i
          implemented yet"})
  end,
  Args = fix_args(hipe_rtl:call_arglist(I)),
  %% Reverse arguments that are passed to stack to match with the Erlang
  %% calling convention(Propably not needed in prim calls).
  ReversedArgs = case erlang:length(Args) > ?AMD64_NR_ARG_REGS of
    false -> Args;
    true -> 
      {ArgsInRegs, ArgsInStack} = lists:split(?AMD64_NR_ARG_REGS, Args),
      ArgsInRegs ++ lists:reverse(ArgsInStack)
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_call_regs(FixedRegs), 
  FinalArgs = case hipe_rtl:call_fun(I) of
		{erlang, get_stacktrace, 0} -> ReversedArgs;
		_ -> fix_reg_args(LoadedFixedRegs) ++ ReversedArgs
	      end,
  {Name, I2, NewRelocs} = case hipe_rtl:call_fun(I) of
    PrimOp when is_atom(PrimOp) -> 
      Name1 = trans_prim_op(PrimOp),
      Relocs1  = relocs_store(Name1, {call, {bif, PrimOp,
                                erlang:length(Args)}}, Relocs),
      {"@"++Name1, [], Relocs1};
    {M, F, A} when is_atom(M), is_atom(F), is_integer(A) ->
      Name1 = trans_mfa_name({M,F,A}),
      Relocs1 = relocs_store(Name1, {call, {M,F,A}}, Relocs),
                              {"@"++Name1, [], Relocs1};
 		Reg ->
      case hipe_rtl:is_reg(Reg) of
        true -> 
          TT1 = mk_temp(),
          {RegName, []} = trans_dst(Reg),
          II1 = hipe_llvm:mk_conversion(TT1, inttoptr, "i64", RegName,
            "i64*"),
          TT2 = mk_temp(),
          II2 = hipe_llvm:mk_conversion(TT2, bitcast, "i64*", TT1,
            "{i64,i64,i64,i64}"++"("++args_to_type(FinalArgs)++")*"),
          {TT2, [II2, II1], Relocs};
        false -> exit({?MODULE, trans_call, {"Unimplemted Call to", Reg}}) 
      end
  end,
  T1 = mk_temp(),
  %% TODO: Fix return type of calls
  I3 = case hipe_rtl:call_fail(I) of
    %% Normal Call
    [] -> hipe_llvm:mk_call(T1, false, "cc 11", [], "{i64, i64, i64, i64}",
			    Name, FinalArgs, []);
    %% Call With Exception
    FailLabelNum -> 
        TrueLabel = "L"++integer_to_list(hipe_rtl:call_normal(I)),
        FailLabel = mk_jump_label(FailLabelNum),
        I4 = hipe_llvm:mk_invoke(T1, "cc 11", [], "{i64, i64, i64, i64}",
				 Name, FinalArgs, [], "%"++TrueLabel, FailLabel),
        I5 = hipe_llvm:mk_label(TrueLabel),
        [I5, I4]
    end,
    I6 = store_call_regs(FixedRegs, T1),
    I7 = case hipe_rtl:call_dstlist(I) of
      [] -> [];
      [_] -> hipe_llvm:mk_extractvalue(Dst, "{i64, i64, i64, i64}", T1, "3", [])
    end,
    I8 = case hipe_rtl:call_continuation(I) of
      [] -> [];
      CC -> {II3, _UnusedRelocs} = trans_goto(hipe_rtl:mk_goto(CC), Relocs),
        II3
    end,
    {[I8, I7, I6, I3, I2, I1], NewRelocs}.

args_to_type(Args) -> 
  Args1 = lists:map(fun (_) -> "i64" end, Args),
  Args2 = lists:foldl(fun (A,B) -> A++","++B end, "", Args1),
  {Args3,_} =lists:split(erlang:length(Args2)-1, Args2),
  Args3.

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
  Args = fix_args(hipe_rtl:enter_arglist(I)),
  %% Reverse arguments that are passed to stack to match with the Erlang
  %% calling convention(Propably not needed in prim calls).
  ReversedArgs = case erlang:length(Args) > ?AMD64_NR_ARG_REGS of
    false -> Args;
    true -> 
      {ArgsInRegs, ArgsInStack} = lists:split(?AMD64_NR_ARG_REGS, Args),
      ArgsInRegs++ lists:reverse(ArgsInStack)
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_call_regs(FixedRegs), 
  FinalArgs = case hipe_rtl:enter_fun(I) of
		{erlang, get_stacktrace, 0} -> ReversedArgs;
		_ -> fix_reg_args(LoadedFixedRegs) ++ ReversedArgs
	      end,
  {Name, I2, NewRelocs} = case hipe_rtl:enter_fun(I) of
    PrimOp when is_atom(PrimOp) -> 
      Name1 = trans_prim_op(PrimOp),
      NewRelocs1  = relocs_store(Name1, {call, {bif, PrimOp,
                                erlang:length(Args)}}, Relocs),
      {"@"++Name1, [], NewRelocs1};
    {M, F, A} when is_atom(M), is_atom(F), is_integer(A) ->
      Name1 = trans_mfa_name({M,F,A}),
      NewRelocs1 = relocs_store(Name1, {call, {M,F,A}}, Relocs),
      {"@"++Name1, [], NewRelocs1};
 		Reg ->
      case hipe_rtl:is_reg(Reg) of
        true -> 
          TT1 = mk_temp(),
          {RegName, []} = trans_dst(Reg),
          II1 = hipe_llvm:mk_conversion(TT1, inttoptr, "i64", RegName,
            "i64*"),
          TT2 = mk_temp(),
          II2 = hipe_llvm:mk_conversion(TT2, bitcast, "i64*", TT1,
            "{i64,i64,i64,i64}"++"("++args_to_type(FinalArgs)++")*"),
          {TT2, [II2, II1], Relocs};
        false -> exit({?MODULE, trans_call, {"Unimplemted Call to", Reg}}) 
      end
  end,
  %% TODO: Fix return type of calls
  T1 = mk_temp(),
  I3 = hipe_llvm:mk_call(T1, true, "cc 11", [], "{i64, i64, i64, i64}",
			 Name, FinalArgs, []),
  I4 = hipe_llvm:mk_ret([{"{i64,i64,i64,i64}", T1}]),
  {[I4, I3, I2, I1], NewRelocs}.

%%
%% fconv
%%
trans_fconv(I, Relocs) ->
  %% XXX: Can a fconv destination be a precoloured reg? 
  _Dst = hipe_rtl:fconv_dst(I),
  {Dst, []} = trans_dst(_Dst),
  _Src = hipe_rtl:fconv_src(I),
  {Src, I1} =  trans_float_src(_Src),
  I2 = hipe_llvm:mk_sitofp(Dst, "i64", Src, "double"),
  {[I2, I1], Relocs}.
    
      
  
%%
%% fixnumop
%%
trans_fixnum(I, Relocs) ->
  Dst = hipe_rtl:fixnumop_dst(I),
  Src = hipe_rtl:fixnumop_src(I),
  I1 = case hipe_rtl:fixnumop_type(I) of
    tag ->
      trans_alu(hipe_tagscheme:realtag_fixnum(Dst, Src), Relocs);
    untag ->
      trans_alu(hipe_tagscheme:realuntag_fixnum(Dst, Src), Relocs)
  end,
  {I1, Relocs}.


%% TODO: fload, fstore, fmove, and fp are almost the same with load,store,move
%% and alu. Maybe we should join them.

%%
%% fload
%% 
trans_fload(I, Relocs) ->
  _Dst = hipe_rtl:fload_dst(I),
  _Src = hipe_rtl:fload_src(I),
  _Offset = hipe_rtl:fload_offset(I),
  {Dst, []} = trans_dst(_Dst),
  {Src, I1} =  trans_float_src(_Src),
  {Offset, I2} = trans_float_src(_Offset),
  T1 = mk_temp(),
  I3 = hipe_llvm:mk_operation(T1, add, "i64", Src, Offset, []),
  T2 = mk_temp(),
  I4 = hipe_llvm:mk_inttoptr(T2, "i64", T1, "double"),
  I5 = hipe_llvm:mk_load(Dst, "double", T2, [], [], false),
  {[I5, I4, I3, I2, I1], Relocs}.

%%
%% fmove
%%
trans_fmove(I, Relocs) -> 
  _Dst = hipe_rtl:fmove_dst(I),
  _Src = hipe_rtl:fmove_src(I),
  IsDstColoured = isPrecoloured(_Dst),
  {Dst, []} = case IsDstColoured of
                true -> {mk_temp(), []};
                false -> trans_dst(_Dst)
            end,
  {Src, I1} = trans_float_src(_Src),
  I2 = hipe_llvm:mk_select(Dst, "true", "double", Src, "double", "undef"),
  I3 = case IsDstColoured of 
    true -> 
      {Dst2, II1} = trans_dst(_Dst),
      II2 = hipe_llvm:mk_store("double", Dst, "double", Dst2, [], [], false),
      [II2, II1];
    false -> []
  end,
  {[I3, I2, I1], Relocs}.

%%
%% fp
%%
trans_fp(I, Relocs) ->
  %% XXX: Just copied trans_alu...think again..
  _Dst = hipe_rtl:fp_dst(I),
  _Src1 = hipe_rtl:fp_src1(I),
  _Src2 = hipe_rtl:fp_src2(I),
  % Destination is a register and not in SSA Form..
  IsDstColoured = isPrecoloured(_Dst),
  {Dst, []} = case IsDstColoured of
    true -> {mk_temp(), []};
    false -> trans_dst(_Dst)
  end,
  {Src1, I1} = trans_float_src(_Src1),
  {Src2, I2} = trans_float_src(_Src2),
  Type = "double",
  Op =  trans_fp_op(hipe_rtl:fp_op(I)),
  I3 = hipe_llvm:mk_operation(Dst, Op, Type, Src1, Src2, []),
  I4 = case IsDstColoured of 
    true -> 
      {Dst2, II1} = trans_dst(_Dst),
      II2 = hipe_llvm:mk_store(Type, Dst, "i64", Dst2, [], [], false),
      [II2, II1];
    false -> []
  end,
  I5 = hipe_llvm:mk_store("double", Dst, "double", "%exception_sync", [] ,[], true),
  T1 = mk_temp(),
  I6 = hipe_llvm:mk_load(T1, "double", "%exception_sync", [], [] ,true),
  {[I6, I5, I4, I3, I2, I1], Relocs}.

%%
%% fp_unop
%%
trans_fp_unop(I, Relocs) ->
  _Dst = hipe_rtl:fp_unop_dst(I),
  _Src = hipe_rtl:fp_unop_src(I),
  % Destination is a register and not in SSA Form..
  IsDstColoured = isPrecoloured(_Dst),
  {Dst, []} = case IsDstColoured of
    true -> mk_temp();
    false -> trans_dst(_Dst)
  end,
  {Src, I1} = trans_float_src(_Src),
  Type = "double",
  Op =  trans_fp_op(hipe_rtl:fp_unop_op(I)),
  I2 = hipe_llvm:mk_operation(Dst, Op, Type, "0.0", Src, []),
  I3 = case IsDstColoured of 
    true -> 
      {Dst2, II1} = trans_dst(_Dst),
      II2 = hipe_llvm:mk_store(Type, Dst, "i64", Dst2, [], [], false),
      [II2, II1];
    false -> []
  end,
  {[I3, I2, I1], Relocs}.
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
  I1 = case hipe_rtl_arch:is_precoloured(Base) of
    true -> trans_fstore_reg(I, Relocs);
    false -> exit({?MODULE, trans_fstore ,{"Non Implemened yet", false}})
  end,
  I1.

trans_fstore_reg(I, Relocs) ->
  B = hipe_rtl:fstore_base(I),
  {Base, _}  = trans_reg(B, dst),
  D1 = mk_hp(),
  I1 = hipe_llvm:mk_load(D1, "i64", Base, [],  [], false),
  D2 = mk_hp(),
  I2 = hipe_llvm:mk_inttoptr(D2, "i64", D1, "double"),
  {_Offset, []} = trans_src(hipe_rtl:fstore_offset(I)),
  Offset =
  integer_to_list(list_to_integer(_Offset) div 8), 
  D3 = mk_hp(),
  I3 = hipe_llvm:mk_getelementptr(D3, "double", D2, [{"i64", Offset}], false),
  _Value = hipe_rtl:fstore_src(I),
  {Value, []} = trans_src(_Value),
  I4 = hipe_llvm:mk_store("double", Value, "double", D3, [], [],
                          false),
  {[I4, I3, I2, I1], Relocs}.

%%
%% gctest
%%
trans_gctest(I, Relocs) ->
  % For now ignore gc_test. Just print it as comment
  {W, []} = trans_src(hipe_rtl:gctest_words(I)),
  I1 = hipe_llvm:mk_comment("gc_test("++W++")"),
  {I1, Relocs}.

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
  {Dst, []} = trans_dst(_Dst),
  {Src, I1} = trans_src(_Src), 
  {Offset, I2} = trans_src(_Offset),
  Type = "i64",
  T1 = mk_temp(),
  I3 = hipe_llvm:mk_operation(T1, add, Type, Src, Offset, []),
  Ins = case hipe_rtl:load_size(I) of 
    word -> 
      T2 = mk_temp(),
      I4 = hipe_llvm:mk_inttoptr(T2, Type, T1, Type),
      I5 = hipe_llvm:mk_load(Dst, Type, T2, [], [], false),
      [I5, I4];
    Size -> 
      LoadType = type_from_size(Size),
      T2 = mk_temp(),
      I4 = hipe_llvm:mk_inttoptr(T2, Type, T1, LoadType),
      T3 = mk_temp(),
      I5 = hipe_llvm:mk_load(T3, LoadType, T2, [], [], false),
      Conversion = case hipe_rtl:load_sign(I) of
        signed -> sext;
        unsigned -> zext
      end,
      I6 = hipe_llvm:mk_conversion(Dst, Conversion, LoadType, T3, "i64"),
      [I6, I5, I4]
  end,
  {[Ins, I3, I2, I1], Relocs}.

%%
%% load_address
%%
trans_load_address(I, Relocs) ->
  %% Check the load_type is constant. We have not implemented other cases yet.
  _Dst = hipe_rtl:load_address_dst(I),
  _Addr = hipe_rtl:load_address_addr(I),
  IsDstColoured = isPrecoloured(_Dst),
  {Dst, []} = case IsDstColoured of
    true -> {mk_temp(), []};
    false -> trans_dst(_Dst)
  end,
  {Addr, NewRelocs} = case hipe_rtl:load_address_type(I) of
    constant -> {"%DL"++integer_to_list(_Addr)++"_var", Relocs};
    closure  -> 
      {Closure, _, _} = _Addr,
      {_, ClosureName, _} = Closure,
      FixedClosurename = atom_to_list(fix_closure_name(ClosureName)),
      Relocs1 = relocs_store(FixedClosurename, {closure,_Addr}, Relocs),
      {"%"++FixedClosurename++"_var", Relocs1};
    type -> exit({?MODULE,trans_load_address, {"Type not implemented in
          load_address", _Addr}})
      end,
  Type = "i64",
  I1 = hipe_llvm:mk_select(Dst, true, Type, Addr, Type, "undef"),
  I2 = case IsDstColoured of 
    true -> 
      {Dst2, II1} = trans_dst(_Dst),
      II2 = hipe_llvm:mk_store(Type, Dst, Type, Dst2, [], [], false),
      [II2, II1];
    false -> []
  end,
  {[I2, I1], NewRelocs}.

%%
%% load_atom
%%
trans_load_atom(I, Relocs) ->
  _Dst = hipe_rtl:load_atom_dst(I),
  _Atom = hipe_rtl:load_atom_atom(I),
  Name = make_llvm_id(atom_to_list(_Atom)),
  Atom_Name = "%"++Name++"_var",
  NewRelocs = relocs_store(Name, {atom, _Atom}, Relocs),
  {Dst, []} = trans_dst(_Dst),
  {hipe_llvm:mk_select(Dst, true, "i64", Atom_Name, "i64", "undef"), NewRelocs}.

%%
%% move
%%
trans_move(I, Relocs) ->
  _Dst = hipe_rtl:move_dst(I),
  _Src = hipe_rtl:move_src(I),
  IsDstColoured = isPrecoloured(_Dst),
  {Dst, []} = case IsDstColoured of
    true -> {mk_temp(), []};
    false -> trans_dst(_Dst)
  end,
  {Src, I1} = trans_src(_Src),
  I2 = hipe_llvm:mk_select(Dst, "true", "i64", Src, "i64", "undef"),
  I3 = case IsDstColoured of 
    true -> 
      {Dst2, II1} = trans_dst(_Dst),
      II2 = hipe_llvm:mk_store("i64", Dst, "i64", Dst2, [], [], false),
      [II2, II1];
    false -> []
  end,
  {[I3, I2, I1], Relocs}.

%% 
%% phi
%%
trans_phi(I, Relocs) ->
  _Dst = hipe_rtl:phi_dst(I),
  {Dst, []} = trans_dst(_Dst),
  I1 = hipe_llvm:mk_phi(Dst , arg_type(_Dst), 
    trans_phi_list(hipe_rtl:phi_arglist(I))),
  {I1, Relocs}.

trans_phi_list([]) -> [];
trans_phi_list([{Label, Value}| Args]) ->
  {Val, []} = trans_src(Value),
  [{Val, mk_jump_label(Label)} | trans_phi_list(Args)].

%%
%% return 
%%
%% TODO: Take care of returning many items
trans_return(I, Relocs) ->
  Ret1 = case hipe_rtl:return_varlist(I) of
    [] -> [];
    [_,_,[]] -> exit({?MODULE, trans_return, "Multiple return not
          implemented"});
    [A|[]] -> 
      {Name, []} = trans_src(A),
      [{"i64", Name}]
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_call_regs(FixedRegs), 
  Ret2 = lists:map(fun(X) -> {"i64", X} end, LoadedFixedRegs),
  Ret = lists:append(Ret2,Ret1),
  [_|[_|Typ]] = lists:foldl(fun(_,Y) -> Y++", i64" end, [],
    Ret),
  Type = "{"++Typ++"}",
  {RetStruct, I2} = mk_return_struct(Ret, Type),
  I3 = hipe_llvm:mk_ret([{Type, RetStruct}]),
  {[I3, I2, I1], Relocs}.

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
  Base = hipe_rtl:store_base(I),
  I1 = case hipe_rtl_arch:is_precoloured(Base) of
    true -> trans_store_reg(I, Relocs);
    false -> trans_store_var(I, Relocs)
  end,
  I1.

trans_store_var(I, Relocs) ->
  {Base, []} = trans_src(hipe_rtl:store_base(I)),
  {Offset, []} = trans_src(hipe_rtl:store_offset(I)), 
  _Value = hipe_rtl:store_src(I),
  {Value, I1} = trans_src(_Value),
  T1 = mk_temp(),
  I2 = hipe_llvm:mk_operation(T1, add, "i64", Base, Offset, []),
  Ins = case hipe_rtl:store_size(I) of 
    word -> 
      T2 = mk_temp(),
      I3 = hipe_llvm:mk_inttoptr(T2, "i64", T1, "i64"),
      I4 = hipe_llvm:mk_store("i64", Value, "i64", T2, [], [], false),
      [I4, I3];
    Size -> 
      %% XXX: Not Tested yet..Is trunc correct ?
      LoadType = type_from_size(Size),
      T2 = mk_temp(),
      I3 = hipe_llvm:mk_inttoptr(T2, "i64", T1, LoadType),
      T3 = mk_temp(),
      I4 = hipe_llvm:mk_conversion(T3, 'trunc', "i64", Value, LoadType),
      I5 = hipe_llvm:mk_store(LoadType, T3, LoadType, T2, [], [], false),
      [I5, I4, I3]
  end,
  {[Ins, I2, I1], Relocs}.

trans_store_reg(I, Relocs) ->
  {Base, _} = trans_reg(hipe_rtl:store_base(I), dst),
  _Value = hipe_rtl:store_src(I),
  {Value, I1} = trans_src(_Value),
  D1 = mk_hp(),
  I2 = hipe_llvm:mk_load(D1, "i64", Base, [],  [], false),
  D2 = mk_hp(),
  I3 = hipe_llvm:mk_inttoptr(D2, "i64", D1, "i64"),
  {_Offset, []} = trans_src(hipe_rtl:store_offset(I)),
  Offset = integer_to_list(list_to_integer(_Offset) div 8), 
  D3 = mk_hp(),
  %% TODO: Fix Size...
  I4 = hipe_llvm:mk_getelementptr(D3, "i64", D2, [{"i64", Offset}], false),
  I5 = hipe_llvm:mk_store("i64", Value, "i64", D3, [], [],
                          false),
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
  I2 = hipe_llvm:mk_switch("i64", Src, lists:nth(length(LabelList)-1, LabelList), ValueLabelList),
  {[I2, I1], Relocs}. 
%%-----------------------------------------------------------------------------


%% When a call has a fail continuation label it must be extended with a normal
%% continuation label to go with the LLVM's invoke instruction. Also all phi
%% nodes that are correlated with the block that holds tha call instruction
%% must be updated
fix_invoke_calls(Code) -> fix_invoke_calls(Code, [], []).
fix_invoke_calls([], Acc, SubstMap) -> 
  Update = fun (X) -> update_phi_nodes(X, SubstMap) end,
  lists:reverse(lists:map(Update, Acc));
fix_invoke_calls([I|Is], Acc, SubstMap) ->
  case I of 
    #call{} ->
      case hipe_rtl:call_fail(I) of
        [] -> fix_invoke_calls(Is, [I|Acc], SubstMap);
        _Label ->
          OldLabel = find_first_label(Acc),
          NewLabel = 9999999999 - hipe_gensym:new_label(rtl),
          NewCall =  hipe_rtl:call_normal_update(I, NewLabel),
          fix_invoke_calls(Is, [NewCall|Acc], [{OldLabel, NewLabel}|SubstMap])
      end;
    _ -> fix_invoke_calls(Is, [I|Acc], SubstMap)
  end.

find_first_label([]) -> exit({?MODULE, find_first_label, "No label found"});
find_first_label([I|Is]) -> 
  case I of
    #label{} -> hipe_rtl:label_name(I);
    _ -> find_first_label(Is)
  end.

update_phi_nodes(I, SubstMap) ->
  case I of
    #phi{} -> update_phi_node(I, SubstMap);
    _ -> I
  end.

update_phi_node(I, []) -> I;
update_phi_node(I, [{OldPred, NewPred} | SubstMap]) ->
  I1 = hipe_rtl:phi_redirect_pred(I, OldPred, NewPred),
  update_phi_node(I1, SubstMap).

%%----------------------------------------------------------------------------


isPrecoloured(X) -> hipe_rtl_arch:is_precoloured(X).

%%is_call(I) -> 
%%  case I of 
%%    #llvm_call{} -> true;
%%    #llvm_invoke{} -> true;
%%    _ -> false
%%  end.
%%
%%call_name(I) ->
%%  case I of 
%%    #llvm_call{} ->
%%      hipe_llvm:call_fnptrval(I);
%%    #llvm_invoke{} ->
%%      hipe_llvm:invoke_fnptrval(I);
%%    Other -> exit({?MODULE, call_name, {"Not a call", Other}})
%%  end.

% Convert RTL argument list to LLVM argument list
fix_args(ArgList) -> lists:map(fun(A) -> {Name, []} = trans_src(A), 
                            {"i64", Name} end, ArgList).

% Convert a list of Precoloured registers to LLVM argument list
fix_reg_args(ArgList) -> lists:map(fun(A) -> {"i64", A} end, ArgList).

reg_not_undef(Name) ->
  case Name of
    "undef" -> false;
    _ -> true
  end.
% Load Precoloured registers.
% Names : Tha name of LLVM temp variables
% Ins   : LLVM Instructions tha achieve the loading
load_call_regs(RegList) -> 
  RegList2 = lists:filter(fun reg_not_undef/1, RegList),
  Names = lists:map(fun mk_temp_reg/1, RegList),
  Names2 = lists:filter(fun reg_not_undef/1, Names), 
  Ins = lists:zipwith(fun (X,Y) -> hipe_llvm:mk_load(X, "i64", "%"++Y++"_reg_var", [], 
                  [], false) end, Names2, RegList2),
  {Names, Ins}.

% Store Precoloured Registers
% Name: The LLVM temp variable name tha holds the struct of return value
store_call_regs(RegList, Name) -> 
  Type = "{i64, i64, i64, i64}",
  RegList2 = lists:filter(fun reg_not_undef/1, RegList),
  Names = lists:map(fun mk_temp_reg/1, RegList),
  Indexes = lists:seq(0, erlang:length(RegList2)-1),
  Names2 = lists:filter(fun reg_not_undef/1, Names), 
  I1 = lists:zipwith(fun(X,Y) -> hipe_llvm:mk_extractvalue(X, Type, Name,
          integer_to_list(Y), [])
    end, Names2, Indexes),
  I2 = lists:zipwith(fun (X,Y) -> hipe_llvm:mk_store("i64", X, "i64",
          "%"++Y++"_reg_var", [], [], false) end, Names2, RegList2),
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
%%mk_hp(N) ->
%%  "%hp_reg_var_" ++ integer_to_list(N).

trans_float_src(Src) -> 
  case hipe_rtl:is_const_label(Src) of
    true ->
      Name = "@DL"++integer_to_list(hipe_rtl:const_label_label(Src)),
      T1 = mk_temp(),
      I1 = hipe_llvm:mk_getelementptr(T1, "i8", Name, [{"i8", "6"}],false),
      T2 = mk_temp(),
      I2 = hipe_llvm:mk_conversion(T2, bitcast, "i8*", T1, "double*"),
      T3 = mk_temp(),
      I3 = hipe_llvm:mk_load(T3, "double", T2, [], [], false),
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
        true -> trans_reg(A, src);
        false -> trans_dst(A)
      end
  end.

trans_dst(A) ->
  case hipe_rtl:is_reg(A) of
    true -> trans_reg(A, dst);
    false ->
      Name = case hipe_rtl:is_var(A) of
        true ->
          "%v" ++ integer_to_list(hipe_rtl:var_index(A));
        false ->
          case hipe_rtl:is_fpreg(A) of
            true -> "%f" ++ integer_to_list(hipe_rtl:fpreg_index(A));
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
  case hipe_rtl_arch:is_precoloured(Arg) of
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
      Type = "i64",
      pointer_from_reg(Name, Type, Offset);
    Name -> 
      {Name, []}
  end.

fix_reg_src(Register) -> 
  case Register of
    {Name, Offset} -> 
      Type = "i64",
      {T1, I1} = pointer_from_reg(Name, Type, Offset),
      T2 = mk_temp(),
      I2 = hipe_llvm:mk_load(T2, Type, T1, [], [] , false),
      {T2, [I2,I1]};
    Name -> 
      T1 = mk_temp(),
      {T1, hipe_llvm:mk_load(T1, "i64", Name, [], [], false)}
  end.

pointer_from_reg(RegName, Type, Offset) ->
      T1 = mk_temp(),
      I1 = hipe_llvm:mk_load(T1, Type, RegName, [], [] ,false),
      T2 = mk_temp(),
      I2 = hipe_llvm:mk_inttoptr(T2, Type, T1, Type),
      T3 = mk_temp(),
      I3 = hipe_llvm:mk_getelementptr(T3, Type, T2, [{Type,
            erlang:integer_to_list(Offset div 8)}], false),
      {T3, [I3, I2, I1]}.
  

%%insn_dst(I) ->
%%  case I of
%%    #alu{} -> hipe_rtl:alu_dst(I);
%%    #alub{} -> hipe_rtl:alub_dst(I);
%%    #call{} -> 
%%      case hipe_rtl:call_dstlist(I) of
%%        [] -> [];
%%        [_, _ |[]] -> exit({?MODULE, insn_dst, {"Call destination list
%%                      not implemented yet", hipe_rtl:call_dstlist(I)}});
%%        [Dst] -> Dst
%%      end;
%%    #load{} -> hipe_rtl:load_dst(I);
%%    #load_address{} -> hipe_rtl:load_address_dst(I);
%%    #load_atom{} -> hipe_rtl:load_atom_dst(I);
%%    %#load_word_index{} -> ok;
%%    #move{} -> hipe_rtl:move_dst(I);
%%    %#multimove{} -> ok;
%%    #phi{} -> hipe_rtl:phi_dst(I);
%%    %#switch{} -> hipe_rtl:switch(I);
%%    _ -> []
%%  end.

type_from_size(Size) -> 
  case Size of
    byte -> "i8";
    int16 -> "i16";
    int32 -> "i32";
    word -> "i64"
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
  %io:format("PRIM OP: ~w~n", [Op]),
  case Op of
    '+' -> "bif_add..";
    '-' -> "bif_sub..";
    '*' -> "bif_mul..";
    'div' -> "bif_div..";
    '/' -> "bif_div..";
    %'rem' -> "srem';
    Other -> atom_to_list(Other)++".."
%    suspend_0 -> "suspend_0..";
%    gc_1 -> "gc_1..";
%    op_exact_eqeq_2 -> "op_exact_eqeq_2..";
%    fwait -> "fwait..";
%    handle_fp_exception -> "handle_fp_exception..";
%    fclearerror_error -> "fclearerror_error..";
%    conv_big_to_float -> "conv_big_to_float..";
%    Other -> exit({?MODULE, trans_prim_op, {"unknown prim op", Other}})
  end.

%% Return the type of arg A (only integers of 64 bits and floats supported).
arg_type(A) ->
  case hipe_rtl:is_fpreg(A) of
    true -> "double";
    _ -> "i64"
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
  Args2 = lists:map( fun(X) -> {"i64", "%v" ++
          integer_to_list(hipe_rtl:var_index(X))}
    end, ReversedParams),
  I1 = hipe_llvm:mk_label("Entry"),
  Exception_Sync = hipe_llvm:mk_alloca("%exception_sync", "double", [], []),
  RegList = lists:filter(fun reg_not_undef/1, Fixed_regs),
  I2 = load_regs(RegList),
  % TODO: Jump to correct label
  I3 = hipe_llvm:mk_br(mk_jump_label(1)),
  Final_Code = lists:flatten([I1, Exception_Sync, I2, LocalVars, I3])++Code,
  [_|[_|Typ]] = lists:foldl(fun(_,Y) -> Y++", i64" end, [],
    Fixed_regs) ,
  Type = "{"++Typ++",i64"++"}",
  hipe_llvm:mk_fun_def([], [], "cc 11", [], Type, FunctionName,
                        Args1++Args2, 
                        [nounwind, noredzone, list_to_atom("gc \"erlang_gc\"")],
                        [],Final_Code).

fixed_registers() ->
  case get(hipe_target_arch) of
    x86 -> [?HP, ?P, ?NSP];
    amd64 ->
      [?HP, ?P, ?NSP];
    Other ->
      exit({?MODULE, map_registers, {"Unknown Architecture", Other}})
  end.

header_regs(Regs) -> header_regs(Regs, []).

header_regs([], Acc) -> lists:reverse(Acc);
header_regs([R|Rs], Acc) ->
  case R of
    "undef" ->
      Reg = {"i64",  mk_temp()},
      header_regs(Rs, [Reg|Acc]);
    _ ->
      Reg = {"i64",  "%"++R++"_in"},
      header_regs(Rs, [Reg|Acc])
  end.

load_regs(Regs) -> load_regs(Regs, []).

load_regs([], Acc) -> Acc;
load_regs([R | Rs], Acc) ->
  I1 = hipe_llvm:mk_alloca("%"++R++"_reg_var", "i64", [], []),
  I2 = hipe_llvm:mk_store("i64", "%"++R++"_in", "i64", "%"++R++"_reg_var", [], [], false),
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
  FunDecl = lists:map(fun call_to_decl/1, ExternalCallList),
  %% Extract constant labels from Constant Map (remove duplicates)
  ConstLabels = lists:usort(find_constants(SlimedConstMap)),
  %% Create code to declare constants 
  ConstDecl = lists:map(fun declare_constant/1, ConstLabels),
  %% Create code to create local name for constants
  ConstLoad = lists:map(fun load_constant/1, ConstLabels),
  %% Enter constants to relocations
  Relocs1 = lists:foldl(fun const_to_dict/2, Relocs, ConstLabels),
  %% Temporary Store inc_stack to Dictionary
  Relocs2 = dict:store("inc_stack_0", {call, {bif, inc_stack_0, 0}}, 
                        Relocs1),
  %% Create LabelMap 
  TempLabelMap = lists:map(fun create_label_map/1, SwitchValues),
  %% Store Swich Jump Tables to reloactions
  Relocs3 = labels_to_dict(TempLabelMap, Relocs2),
  ExternalDeclarations = AtomDecl++ClosureDecl++ConstDecl++FunDecl,
  LocalVariables = AtomLoad++ClosureLoad++ConstLoad,
  {Relocs3, ExternalDeclarations, LocalVariables, TempLabelMap}.

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
  hipe_llvm:mk_const_decl("@"++AtomName, "external constant", "i64", "").

%% Creation of local variable for an atom 
load_atom({AtomName, _}) ->
  Dst = "%"++AtomName++"_var",
  Name = "@"++AtomName,
  hipe_llvm:mk_ptrtoint(Dst, "i64", Name, i64).

%% External declaration of a closure
declare_closure({ClosureName, _})->
  hipe_llvm:mk_const_decl("@"++ClosureName, "external constant", "i8", "").

%% Creation of local variable for a closure
load_closure({ClosureName, _})->
  Dst = "%"++ClosureName++"_var",
  Name = "@"++ClosureName,
  hipe_llvm:mk_ptrtoint(Dst, "i8", Name, "i64").

%% A call is treated as non external only in a case of a recursive function
is_external_call({_, {call, Fun}}, Fun) -> false;
is_external_call(_, _) -> true.

%% External declaration of a function
call_to_decl({Name, {call, MFA}}) -> 
  {M, F, A} = MFA,
  Cconv = "cc 11",
  {Type, Args} = case M of
    llvm -> {"{i64, i1}", lists:seq(1,2)};
    erlang ->
      case F of 
        get_stacktrace -> {"{i64,i64,i64,i64}", []};
        %% +3 for precoloured regs
        _ -> {"{i64,i64,i64,i64}", lists:seq(1,A+3)}
      end;
    %% +3 for precoloured regs
    _ -> {"{i64,i64,i64,i64}", lists:seq(1,A+3)}
  end,
  Args_type = lists:map(fun(_) -> "i64" end, Args),
  hipe_llvm:mk_fun_decl([], [], Cconv, [], Type, "@"++Name, Args_type, []). 

%% Create NewData which contains blocks for JumpTables. Also
%% return necessary information to create LabelMap
data_from_switches([], NewData, SortedBy) -> {NewData, SortedBy};
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
      io:format("J Tab Lab ~w ~n", [JTabLab]),
      data_from_switches(Is, NewData, [{JTabLab, hipe_rtl:switch_sort_order(I)}|Sorted]);
    _ -> data_from_switches(Is, Data, Sorted)
  end.

create_label_map([]) -> [];
create_label_map({_, []}=LM) -> LM;
create_label_map({ConstNumber, SortOrder}) -> {ConstNumber, sorted,
    length(SortOrder)*8,SortOrder}.

labels_to_dict(TempLabelMap, Dict) ->
  labels_to_dict(TempLabelMap, Dict, 0).

labels_to_dict([], Dict,_) -> Dict;
labels_to_dict([{ConstNumber, []}|Rest], Dict, RodataNumber) ->
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
  hipe_llvm:mk_const_decl(Name, "external constant", "i8", "").

%% Loading of a constant depends on it's type. Float constants are loaded
%% to double (with offset 6?), and all other constants are converted from
%% pointers to 64 integers.
load_constant(Label) ->
  Dst = "%DL"++integer_to_list(Label)++"_var",
  Name = "@DL"++integer_to_list(Label),
  hipe_llvm:mk_ptrtoint(Dst, "i8", Name, "i64").


%% Store external constants and calls to dictionary
const_to_dict(Elem, Dict) ->
  Name = "DL"++integer_to_list(Elem),
  dict:store(Name, {'constant', Elem}, Dict).
