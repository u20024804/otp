%% -*- erlang-indent-level: 2 -*-

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").
-include("hipe_llvm.hrl").
-include("../rtl/hipe_literals.hrl").
-export([translate/1]).

-define(HP, "hp").
-define(P, "p").
-define(NSP, "nsp").

-ifdef(AMD64_FCALLS_IN_REGISTER).
-define(FCALLS, "fcalls").
-else.
-define(FCALLS, "undef").
-endif.

-ifdef(AMD64_HEAP_LIMIT_IN_REGISTER).
-define(HEAP_LIMIT, "heap_limit").
-else.
-define(HEAP_LIMIT, "undef").
-endif.

-define(HIPE_X86_REGISTERS, hipe_amd64_registers).

translate(RTL) ->
  hipe_gensym:init(llvm),
  Data = hipe_rtl:rtl_data(RTL),
  Code = hipe_rtl:rtl_code(RTL),
  Fun =  hipe_rtl:rtl_fun(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  %% To be used later
  _IsClosure = hipe_rtl:rtl_is_closure(RTL),
  _IsLeaf = hipe_rtl:rtl_is_leaf(RTL),
%  io:format("Geia sou llvm!~n"),
  {Mod_Name, Fun_Name, Arity} = Fun,
  %% Print RTL to file
  {ok, File_rtl} = file:open(atom_to_list(Fun_Name) ++ ".rtl", [write]),
  hipe_rtl:pp(File_rtl, RTL),
  file:close(File_rtl),
  %% Create constant map and write it to file for loader
  {ConstAlign,ConstSize,ConstMap,RefsFromConsts} =
  hipe_pack_constants:pack_constants([{Fun, [], Data}], ?HIPE_X86_REGISTERS:alignment()),
  SC = hipe_pack_constants:slim_constmap(ConstMap),
  file:write_file(atom_to_list(Fun_Name) ++ "_" ++ integer_to_list(Arity) ++ 
    "_constmap.o", erlang:term_to_binary(SC), [binary]),
%  io:format("--> RTL2LLVM: FINAL CONSTMAP:~n~w~n<--~n", [SC]),
  %% Extract constant labels from Constant Map (remove duplicates)
  ConstLabels = lists:usort(find_constants(SC)),
%  io:format("--> RTL2LLVM: Constant Labels Found: ~w~n", [ConstLabels]),
  %% Extract atoms from RTL Code(remove duplicates)
  Atoms = lists:usort(find_atoms(Code)),
%  io:format("--> RTL2LLVM Atoms Found ~w~n", [Atoms]),
  %% Create code to declare atoms
  AtomDecl = lists:map(fun declare_atom/1, Atoms),
  %% Create code to create local name for atoms
  AtomLoad = lists:map(fun load_atom/1, Atoms),
  %% Create code to declare constants 
  ConstDecl = lists:map(fun declare_constant/1, ConstLabels),
  %% Create code to create local name for constants
  ConstLoad = lists:map(fun load_constant/1, ConstLabels),
  LLVM_Code = translate_instr_list(Code, []),
  LLVM_Code2 = create_header(Fun, Params, LLVM_Code, AtomLoad++ConstLoad),
  %% Find function calls in code
  Is_call = fun (X) -> is_external_call(X, atom_to_list(Mod_Name),
        atom_to_list(Fun_Name), integer_to_list(Arity)) end,
  I1 = lists:filter(fun is_call/1, LLVM_Code),
  I2 = lists:filter(Is_call, I1),
  %% Create code to declare external function
  Fun_Declarations = lists:map(fun call_to_decl/1, I2),
  LLVM_Code3 = AtomDecl++ConstDecl++[LLVM_Code2|Fun_Declarations],
  CallDict = dict:new(),
  CallDict2 = lists:foldl(fun call_to_dict/2, CallDict, I1),
  CallDict3 = lists:foldl(fun const_to_dict/2, CallDict2, ConstLabels),
  CallDict4 = lists:foldl(fun atom_to_dict/2, CallDict3, Atoms),
  %% Temporary Store inc_stack to Dictionary
  CallDict5 = dict:store("@inc_stack_0", {inc_stack_0}, CallDict4),
  {LLVM_Code3, CallDict5}.

%%-----------------------------------------------------------------------------

%% Extract Atoms from RTL Code
find_atoms(Code) -> find_atoms(Code, []).
find_atoms([], Atoms) -> Atoms;
find_atoms([I|Is], Atoms) -> 
  case I of
    #load_atom{} ->
      Atom = hipe_rtl:load_atom_atom(I),
      find_atoms(Is, [Atom|Atoms]);
    _ -> find_atoms(Is, Atoms)
  end.

declare_atom(Atom) ->
  Name = "@"++atom_to_list(Atom),
  hipe_llvm:mk_const_decl(Name, "external constant", "i64", "").
load_atom(Atom) ->
  Dst = "%"++atom_to_list(Atom)++"_var",
  Name = "@"++atom_to_list(Atom),
  hipe_llvm:mk_ptrtoint(Dst, "i64", Name, i64).
atom_to_dict(Atom, Dict) ->
  Name = "@"++atom_to_list(Atom),
  dict:store(Name, {'atom', Atom}, Dict).

      
%% Extracts Constant Labels from ConstMap
find_constants(ConstMap) -> find_constants(ConstMap, []).
find_constants([], ConstLabels) -> ConstLabels;
find_constants([Label, _, _, _| Rest], ConstLabels) -> find_constants(Rest,
    [Label|ConstLabels]).

declare_constant(Label) -> 
  Name = "@DL"++integer_to_list(Label),
  hipe_llvm:mk_const_decl(Name, "external constant", "i64", "").

load_constant(Label) ->
  Dst = "%DL"++integer_to_list(Label)++"_var",
  Name = "@DL"++integer_to_list(Label),
  hipe_llvm:mk_ptrtoint(Dst, "i64", Name, i64).

const_to_dict(Elem, Dict) ->
  Name = "@DL"++integer_to_list(Elem),
  dict:store(Name, {'constant', Elem}, Dict).

call_to_dict(Elem, Dict) -> 
  Name = hipe_llvm:call_fnptrval(Elem),
  case re:run(Name, "@([a-z_0-9]*)\.([a-z_0-9]*)\.([a-z_0-9]*)",
      [global,{capture,all_but_first,list}]) of
    {match, [[BifName, [], []]]} -> 
      dict:store(Name, {erlang:list_to_atom(BifName)}, Dict);
    {match, [[M,F,A]]} -> 
      case M of
        "llvm" -> Dict;
        _ -> dict:store(Name, {erlang:list_to_atom(M),
                        erlang:list_to_atom(F),
                        erlang:list_to_integer(A)}, Dict)
                end;
    {match, _} -> Dict;
    nomatch -> 
      exit({?MODULE, call_to_dict, {"Unknown call",Name}})
  end.

translate_instr_list([], Acc) -> 
  lists:reverse(lists:flatten(Acc));
translate_instr_list([I|Is], Acc) ->
  Acc1 = translate_instr(I),
  translate_instr_list(Is, [Acc1|Acc]).


translate_instr(I) ->
  case I of
    #alu{} -> trans_alu(I);
    #alub{} -> trans_alub(I);
    #branch{} -> trans_branch(I);
    #call{} -> trans_call(I);
    #comment{} -> trans_comment(I);
    #enter{} -> trans_enter(I);
    %#fconv{} -> ok;
    #fixnumop{} -> trans_fixnum(I);
    %#fload{} -> ok;
    %#fmove{} -> ok;
    %#fp{} -> ok;
    %#fp_unop{} -> ok;
    %#fstore{} -> ok;
    #gctest{} -> trans_gctest(I);
    #goto{} -> trans_goto(I);
    %#goto_index{} -> ok;
    #label{} -> trans_label(I);
    #load{} -> trans_load(I);
    #load_address{} -> trans_load_address(I);
    #load_atom{} -> trans_load_atom(I);
    %#load_word_index{} -> ok;
    #move{} -> trans_move(I);
    %#multimove{} -> ok;
    #phi{} -> trans_phi(I);
    #return{} -> trans_return(I);
    #store{} -> trans_store(I);
    #switch{} -> trans_switch(I);
    Other -> 
      exit({?MODULE, translate_instr, {"unknown RTL instruction", Other}})
  end.

%%-----------------------------------------------------------------------------

%%
%% alu
%% 
trans_alu(I) ->
  _Dst = hipe_rtl:alu_dst(I),
  _Src1 = hipe_rtl:alu_src1(I),
  _Src2 = hipe_rtl:alu_src2(I),
  % Destination is a register and not in SSA Form..
  Dst = case isPrecoloured(_Dst) of
    true -> mk_temp();
    false -> trans_dst(_Dst)
  end,
  {Src1, I1} = 
  case isPrecoloured(_Src1) of
    true -> 
      fix_reg_src(_Src1);
      %T1 = mk_temp(),
      %{T1, hipe_llvm:mk_load(T1, "i64", trans_src(_Src1), [], [], false)};
    false ->
      {trans_src(_Src1), []}
  end,
  {Src2, I2} = 
  case isPrecoloured(_Src2) of
    true -> 
      fix_reg_src(_Src2);
      %T2 = mk_temp(),
      %{T2, hipe_llvm:mk_load(T2, "i64", trans_src(_Src2), [], [], false)};
    false ->
      {trans_src(_Src2), []}
  end,
  Type = arg_type(_Src1),
  Op =  trans_op(hipe_rtl:alu_op(I)),
  I3 = hipe_llvm:mk_operation(Dst, Op, Type, Src1, Src2, []),
  I4 = case isPrecoloured(_Dst) of 
    true -> 
      {Dst2, Ins} = fix_reg_dst(_Dst),
      Ins2 = hipe_llvm:mk_store(Type, Dst, Type, Dst2, [], [], false),
      [Ins2, Ins];
    false -> []
  end,
  [I4, I3, I2, I1].
          
%%
%% alub
%%
trans_alub(I) ->
  case hipe_rtl:alub_cond(I) of
    overflow -> trans_alub_overflow(I);
    not_overflow -> trans_alub_overflow(I);
    _ -> trans_alub_no_overflow(I)
  end.

trans_alub_overflow(I) ->
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  Src1 =  trans_src(hipe_rtl:alub_src1(I)),
  Src2 =  trans_src(hipe_rtl:alub_src2(I)),
  %TODO: Fix call
  Name = case hipe_rtl:alub_op(I) of
    add -> "@llvm.sadd.with.overflow.i64";
    mul -> "@llvm.smul.with.overflow.i64";
    sub -> "@llvm.ssub.with.overflow.i64";
      _ -> exit({?MODULE, trans_alub_overflow, I})
    end,
  I1 = hipe_llvm:mk_call(T1, false, [], [], "{i64, i1}", Name,
    [{"i64", Src1},{"i64", Src2}], []),
  %
  Dst = trans_dst(hipe_rtl:alub_dst(I)),
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
  [I4, I3, I2, I1].

trans_alub_no_overflow(I) ->
  %alu
  T = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
    hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  I1 = trans_alu(T),
  %icmp
  _Dst = hipe_rtl:alub_dst(I),
  {Dst, I2} = case isPrecoloured(_Dst) of
    true -> fix_reg_src(_Dst);
    false -> {trans_dst(_Dst), []}
  end,
  _Src1 = hipe_rtl:alub_src1(I),
  _Src2 = hipe_rtl:alub_src2(I),
  {Src1, I3} = 
  case isPrecoloured(_Src1) of
    true -> 
      fix_reg_src(_Src1);
      %T1 = mk_temp(),
      %{T1, hipe_llvm:mk_load(T1, "i64", trans_src(_Src1), [], [], false)};
    false ->
      {trans_src(_Src1), []}
  end,
  {Src2, I4} = 
  case isPrecoloured(_Src2) of
    true -> 
      fix_reg_src(_Src2);
      %T2 = mk_temp(),
      %{T2, hipe_llvm:mk_load(T2, "i64", trans_src(_Src2), [], [], false)};
    false ->
      {trans_src(_Src2), []}
  end,
  Type = arg_type(hipe_rtl:alub_src1(I)),
  Cond = trans_rel_op(hipe_rtl:alub_cond(I)),
  T3 = mk_temp(),
  I5 = hipe_llvm:mk_icmp(T3, Cond, Type, Dst, "0"),
  %br
  True_label = mk_jump_label(hipe_rtl:alub_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:alub_false_label(I)),
  I6 = hipe_llvm:mk_br_cond(T3, True_label, False_label),
  [I6, I5, I4, I3, I2, I1].

%%
%% branch
%%
trans_branch(I) ->
  Type = arg_type(hipe_rtl:branch_src1(I)),
  Src1 = trans_src(hipe_rtl:branch_src1(I)),
  Src2 = trans_src(hipe_rtl:branch_src2(I)),
  Cond = trans_rel_op(hipe_rtl:branch_cond(I)),
  %icmp
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  I1 = hipe_llvm:mk_icmp(T1, Cond, Type, Src1, Src2),
  %br
  True_label = mk_jump_label(hipe_rtl:branch_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:branch_false_label(I)),
  I2 = hipe_llvm:mk_br_cond(T1, True_label, False_label),
  [I2, I1].

%%
%% call
%%
trans_call(I) ->
  I1 = case hipe_rtl:call_fun(I) of
    Prim when is_atom(Prim) ->
      trans_prim_call(I);
    {M,F,A} when is_atom(M), is_atom(F), is_integer(A) ->
      trans_mfa_call(I)
  end,
  I2 = case hipe_rtl:call_continuation(I) of
    [] -> [];
    CC -> trans_goto(hipe_rtl:mk_goto(CC))
  end,
  %% TODO: Fail call continuation
  case hipe_rtl:call_fail(I) of 
    [] -> ok;
    FC when erlang:is_integer(FC)-> exit({?MODULE, trans_call, "Fail Continuation Not Implemented Yet"})
  end,
  [I2, I1].


%TODO: Fix Return Type of calls.
trans_prim_call(I) ->
  Dst = case hipe_rtl:call_dstlist(I) of
    [] -> mk_temp();
    [Destination] -> trans_dst(Destination);
    [D|Ds] -> exit({?MODULE, trans_prim_call, "Destination list not i
          implemented yet"})
  end,
  Args = fix_args(hipe_rtl:call_arglist(I)),
  %% Reverse arguments that are passed to stack to match with the Erlang
  %% calling convention(Propably not needed in prim calls).
  ReversedArgs = case erlang:length(Args) > ?AMD64_NR_ARG_REGS of
    false -> Args;
    true -> 
      {ArgsInRegs, ArgsInStack} = lists:split(?AMD64_NR_ARG_REGS, Args),
      ArgsInRegs++lists:reverse(ArgsInStack)
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_call_regs(FixedRegs), 
  FinalArgs = fix_reg_args(LoadedFixedRegs) ++ ReversedArgs,
  Op = trans_prim_op(hipe_rtl:call_fun(I)),
  T1 = mk_temp(),
  I2 = hipe_llvm:mk_call(T1, false, "cc 11", [], "{i64, i64, i64, i64, i64,
    i64}", "@"++Op, FinalArgs, []),
  I3 = store_call_regs(FixedRegs, T1),
  I4 = case hipe_rtl:call_dstlist(I) of
    [] -> [];
    [_] -> hipe_llvm:mk_extractvalue(Dst, "{i64, i64, i64, i64, i64,
    i64}", T1, "5", [])
  end,
  [I4, I3, I2, I1].


trans_mfa_call(I) ->
  Dst = case hipe_rtl:call_dstlist(I) of
    [] -> mk_temp();
    [Destination] -> trans_dst(Destination);
    [D|Ds] -> exit({?MODULE, trans_prim_call, "Destination list not implemented
          yet"})
  end,
  Args = fix_args(hipe_rtl:call_arglist(I)),
  %% Reverse arguments that are passed to stack to match with the Erlang
  %% calling convention
  ReversedArgs = case erlang:length(Args) > ?AMD64_NR_ARG_REGS of
    false -> Args;
    true -> 
      {ArgsInRegs, ArgsInStack} = lists:split(?AMD64_NR_ARG_REGS, Args),
      ArgsInRegs++lists:reverse(ArgsInStack)
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_call_regs(FixedRegs), 
  FinalArgs = fix_reg_args(LoadedFixedRegs) ++ ReversedArgs,
  Name = trans_mfa_name(hipe_rtl:call_fun(I)),
  T1 = mk_temp(),
  I2 = hipe_llvm:mk_call(T1, false, "cc 11", [], "{i64, i64, i64, i64, i64, 
                        i64}", Name, FinalArgs, []),
  I3 = store_call_regs(FixedRegs, T1),
  I4 = case hipe_rtl:call_dstlist(I) of
    [] -> [];
    [_] ->  hipe_llvm:mk_extractvalue(Dst, "{i64, i64, i64, i64,
        i64, i64}", T1, "5", [])
  end,
  [I4, I3, I2, I1].


%%
%% trans_comment
%%
trans_comment(I) ->
  I1 = hipe_llvm:mk_comment(hipe_rtl:comment_text(I)),
  I1.


%%
%% enter
%%
trans_enter(I) ->
  %For now treat it as normal call
  Foo = hipe_rtl:mk_new_var(),
  I1 = hipe_rtl:mk_call(
    [Foo],
    hipe_rtl:enter_fun(I),
    hipe_rtl:enter_arglist(I),
    [],
    [],
    hipe_rtl:enter_type(I)
  ),
  I2 = hipe_rtl:mk_return([Foo]),
  [trans_return(I2), trans_call(I1)].
    
      
  
%%
%% fixnumop
%%
trans_fixnum(I) ->
  Dst = hipe_rtl:fixnumop_dst(I),
  Src = hipe_rtl:fixnumop_src(I),
  I1 = case hipe_rtl:fixnumop_type(I) of
    tag ->
      trans_alu(hipe_tagscheme:realtag_fixnum(Dst, Src));
    untag ->
      trans_alu(hipe_tagscheme:realuntag_fixnum(Dst, Src))
  end,
  I1.

%%
%% gctest
%%
trans_gctest(I) ->
  % For now ignore gc_test. Just print it as comment
  W = trans_src(hipe_rtl:gctest_words(I)),
  I1 = hipe_llvm:mk_comment("gc_test("++W++")"),
  I1.

%%
%% goto
%%
trans_goto(I) ->
  I1 = hipe_llvm:mk_br(mk_jump_label(hipe_rtl:goto_label(I))),
  I1.

%%
%% label
%%
trans_label(I) ->
  Label  = mk_label(hipe_rtl:label_name(I)),
  I1 = hipe_llvm:mk_label(Label),
  I1.

%%
%% load
%%
trans_load(I) ->
  _Dst = hipe_rtl:load_dst(I),
  _Src = hipe_rtl:load_src(I),
  Size = hipe_rtl:load_size(I),
  _Offset = hipe_rtl:load_offset(I),
  Dst = trans_dst(_Dst),
  {Src, I1} = 
  case isPrecoloured(_Src) of
    true -> 
      fix_reg_src(_Src);
    false ->
      {trans_src(_Src), []}
  end,
  {Offset, I2} = 
  case isPrecoloured(_Offset) of
    true -> 
      fix_reg_src(_Offset);
    false ->
      {trans_src(_Offset), []}
  end,
  Type = arg_type(_Src),
  T1 = mk_temp(),
  I3 = hipe_llvm:mk_operation(T1, add, Type, Src, Offset, []),
  T2 = mk_temp(),
  I4 = hipe_llvm:mk_inttoptr(T2, Type, T1, Type),
  T3 = mk_temp(),
  I5 = hipe_llvm:mk_load(T3, Type, T2, [], [], false),
  I6 = hipe_llvm:mk_select(Dst, true, Type, T3, Type, "undef"),
  [I6, I5, I4, I3, I2, I1].

%%
%% load_address
%%
trans_load_address(I) ->
  %% Check the load_type is constant. We have not implemented other cases yet.
  _Dst = hipe_rtl:load_address_dst(I),
  _Addr = hipe_rtl:load_address_addr(I),
  Dst = case isPrecoloured(_Dst) of
    true -> mk_temp();
    false -> trans_dst(_Dst)
  end,
  Addr = case hipe_rtl:load_address_type(I) of
    constant -> "%DL"++integer_to_list(_Addr)++"_var";
    _ -> exit({?MODULE,trans_load_address, "Type not implemented in
          load_address"})
      end,
  Type = "i64",
  I1 = hipe_llvm:mk_select(Dst, true, Type, Addr, Type, "undef"),
  I2 = case isPrecoloured(_Dst) of 
    true -> 
      {Dst2, Ins} = fix_reg_dst(_Dst),
      Ins2 = hipe_llvm:mk_store(Type, Dst, Type, Dst2, [], [], false),
      [Ins2, Ins];
    false -> []
  end,
  [I2, I1].
%%
%% load_atom
%%
trans_load_atom(I) ->
  _Dst = hipe_rtl:load_atom_dst(I),
  _Atom = hipe_rtl:load_atom_atom(I),
  Atom_Name = "%"++atom_to_list(_Atom)++"_var",
  Dst = trans_dst(_Dst),
  hipe_llvm:mk_select(Dst, true, "i64", Atom_Name, "i64", "undef").
%%
%% move
%%
trans_move(I) ->
  _Dst = hipe_rtl:move_dst(I),
  _Src = hipe_rtl:move_src(I),
  Dst = case isPrecoloured(_Dst) of
    true -> mk_temp();
    false -> trans_dst(_Dst)
  end,
  {Src, I1} = 
  case isPrecoloured(_Src) of
    true -> 
      fix_reg_src(_Src);
    false ->
      {trans_src(_Src), []}
  end,
  I2 = hipe_llvm:mk_select(Dst, "true", "i64", Src, "i64", "undef"),
  I3 = case isPrecoloured(_Dst) of 
    true -> 
      {Dst2, Ins} = fix_reg_dst(_Dst),
      Ins2 = hipe_llvm:mk_store("i64", Dst, "i64", Dst2, [], [], false),
      [Ins2, Ins];
    false -> []
  end,
  [I3, I2, I1].

%% 
%% phi
%%
trans_phi(I) ->
  Dst = hipe_rtl:phi_dst(I),
  I1 = hipe_llvm:mk_phi(trans_dst(Dst) , arg_type(Dst), 
    trans_phi_list(hipe_rtl:phi_arglist(I))),
  I1.

trans_phi_list([]) -> [];
trans_phi_list([{Label, Value}| Args]) ->
  [{trans_src(Value), mk_jump_label(Label)} | trans_phi_list(Args)].

%%
%% return 
%%
%% TODO: Take care of returning many items
trans_return(I) ->
  Ret1 = case hipe_rtl:return_varlist(I) of
    [] -> [];
    [A,B,[]] -> exit({?MODULE, trans_return, "Multiple return not
          implemented"});
    [A|[]] -> [{arg_type(A), trans_src(A)}]
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_call_regs(FixedRegs), 
  Ret2 = lists:map(fun(X) -> {"i64", X} end, LoadedFixedRegs),
  Ret = lists:append(Ret2,Ret1),
  I2 = hipe_llvm:mk_ret(Ret),
  [I2, I1].



%%
%% store 
%%
trans_store(I) ->
  Base = hipe_rtl:store_base(I),
  I1 = case hipe_rtl_arch:is_precoloured(Base) of
    true -> trans_store_reg(I);
    false -> exit({?MODULE, trans_store ,{"Non Implemened yet", I}})
  end,
  I1.

trans_store_reg(I) ->
  B = hipe_rtl:store_base(I),
  Base  = trans_reg(B),
  D1 = mk_hp(),
  I1 = hipe_llvm:mk_load(D1, "i64", Base, [],  [], false),
  D2 = mk_hp(),
  I2 = hipe_llvm:mk_inttoptr(D2, "i64", D1, "i64"),
  Offset =
  integer_to_list(list_to_integer(trans_src(hipe_rtl:store_offset(I))) div 8), 
  D3 = mk_hp(),
  I3 = hipe_llvm:mk_getelementptr(D3, "i64", D2, [{"i64", Offset}], false),
  Value = hipe_rtl:store_src(I),
  I4 = hipe_llvm:mk_store("i64", trans_src(Value), "i64", D3, [], [],
                          false),
  [I4, I3, I2, I1].

%%
%% switch
%%
trans_switch(I) ->
  _Src = hipe_rtl:switch_src(I),
  {Src, I1} = 
  case isPrecoloured(_Src) of
    true -> 
      fix_reg_src(_Src);
    false ->
      {trans_src(_Src), []}
  end,
  LabelList = lists:map(fun mk_jump_label/1, hipe_rtl:switch_labels(I)),
  ValueList = lists:map(fun integer_to_list/1, hipe_rtl:switch_sort_order(I)),
  ValueLabelList = lists:zip(ValueList, LabelList),
  I2 = hipe_llvm:mk_switch("i64", Src, lists:nth(1, LabelList), ValueLabelList),
  [I2, I1]. 
%%-----------------------------------------------------------------------------

isPrecoloured(X) -> hipe_rtl_arch:is_precoloured(X).

is_call(I) -> 
  case I of 
    #llvm_call{} -> true;
    _ -> false
  end.

is_external_call(I, M, F, A) -> 
  case I of
    #llvm_call{} -> 
      Name = hipe_llvm:call_fnptrval(I),
      case re:run(Name, "@([a-z_0-9]*)\.([a-z_0-9]*)\.([a-z_0-9]*)",
          [global,{capture,all_but_first,list}]) of
        {match, [[M,F,A]]} -> %io:format("Yo1"),
          false;
        _ -> true
      end;
    _ -> false
  end.

call_to_decl(A) -> 
  Cconv = hipe_llvm:call_cconv(A),
  Type = hipe_llvm:call_type(A),
  Name = hipe_llvm:call_fnptrval(A),
  Args_type = lists:map(fun({X,Y}) -> X end, hipe_llvm:call_arglist(A)),
    hipe_llvm:mk_fun_decl([], [], Cconv, [], Type, Name, Args_type, []). 


% Convert RTL argument list to LLVM argument list
fix_args(ArgList) -> lists:map(fun(A) -> {"i64", trans_src(A)} end, ArgList).

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
  Ins = lists:zipwith(fun (X,Y) -> hipe_llvm:mk_load(X, "i64", "%"++Y++"_var", [], 
                  [], false) end, Names2, RegList2),
  {Names, Ins}.

% Store Precoloured Registers
% Name: The LLVM temp variable name tha holds the struct of return value
store_call_regs(RegList, Name) -> 
  Type = "{i64, i64, i64, i64, i64, i64}",
  RegList2 = lists:filter(fun reg_not_undef/1, RegList),
  Names = lists:map(fun mk_temp_reg/1, RegList),
  Indexes = lists:seq(0, erlang:length(RegList2)-1),
  Names2 = lists:filter(fun reg_not_undef/1, Names), 
  I1 = lists:zipwith(fun(X,Y) -> hipe_llvm:mk_extractvalue(X, Type, Name,
          integer_to_list(Y), [])
    end, Names2, Indexes),
  I2 = lists:zipwith(fun (X,Y) -> hipe_llvm:mk_store("i64", X, "i64",
          "%"++Y++"_var", [], [], false) end, Names2, RegList2),
  [I2, I1].

fix_name(Name) ->
  case Name of
    '++' -> concat;
    Other -> Other
  end.

trans_mfa_name({M,F,A}) ->
  "@"++atom_to_list(M)++"."++atom_to_list(fix_name(F))++"."++integer_to_list(A).

mk_num() -> integer_to_list(hipe_gensym:new_var(llvm)).

mk_label(N) ->
  "L" ++ integer_to_list(N).

mk_jump_label(N) ->
  "%L" ++ integer_to_list(N).

mk_temp() ->
  "%t" ++ integer_to_list(hipe_gensym:new_var(llvm)).
mk_temp(N) ->
  "%t" ++ integer_to_list(N).

mk_temp_reg(Name) -> 
  case reg_not_undef(Name) of
    true -> "%"++Name++integer_to_list(hipe_gensym:new_var(llvm));
    false -> "undef"
  end.

mk_hp() ->
  "%hp_var_" ++ integer_to_list(hipe_gensym:new_var(llvm)).
mk_hp(N) ->
  "%hp_var_" ++ integer_to_list(N).

%% Translate source and destination arguments
trans_src(A) ->
  case hipe_rtl:is_imm(A) of
    true ->  integer_to_list(hipe_rtl:imm_value(A));
    false -> trans_dst(A)  
  end.

trans_dst(A) ->
  case hipe_rtl:is_var(A) of
    true ->
      "%v" ++ integer_to_list(hipe_rtl:var_index(A));
    false ->
      case hipe_rtl:is_reg(A) of
        true ->
          trans_reg(A);
        false ->
          case hipe_rtl:is_const_label(A) of
            true ->
              "%DL"++integer_to_list(hipe_rtl:const_label_label(A))++"_var";
            false -> exit({?MODULE, trans_dst, {"bad RTL arg",A}})
          end
      end
  end.

%% Translate register. If it is precoloured it must be mapped to some llvm var
%% that corresponds to an argument
trans_reg(Arg) ->
  Index = hipe_rtl:reg_index(Arg),
  case hipe_rtl_arch:is_precoloured(Arg) of
    true -> map_precoloured_reg(Index);
    false -> hipe_rtl_arch:reg_name(Index)
  end.

map_precoloured_reg(Index) ->
  %TODO : Works only for amd64 architecture and only for register r15
  case hipe_rtl_arch:reg_name(Index) of
    "%r15" -> "%hp_var";
    "%rbp" -> "%p_var";
    "%fcalls" -> {"%p_var", hipe_amd64_registers:proc_offset(hipe_amd64_registers:fcalls())};
    "%hplim" -> {"%p_var", hipe_amd64_registers:proc_offset(hipe_amd64_registers:heap_limit())};
    _ ->  exit({?MODULE, map_precoloured_reg, {"Register not mapped yet",
            Index}})
  end.

fix_reg_dst(Reg) ->
  case trans_src(Reg) of
    {Name, Offset} -> 
      Type = "i64",
      pointer_from_reg(Name, Type, Offset);
    Name -> 
      {Name, []}
  end.

fix_reg_src(Reg) -> 
  case trans_src(Reg) of
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
    suspend_0 -> "suspend_0..";
    gc_1 -> "gc_1..";
    op_exact_eqeq_2 -> "op_exact_eqeq_2..";
    Other -> exit({?MODULE, trans_prim_op, {"unknown prim op", Other}})
  end.

%% Return the type of arg A (only integers of 32 bits supported).
arg_type(A) ->
  case hipe_rtl:is_var(A) of
    true -> "i64";
    false ->
      case hipe_rtl:is_reg(A) of
        true -> "i64";
        false -> "i64"
      end
  end.

%%-----------------------------------------------------------------------------

%% Create Header for Function 

create_header(Name, Params, Code, ConstLoad) ->
  % TODO: What if arguments more than available registers?
  % TODO: Jump to correct label
  {Mod_Name,Fun_Name,Arity} = Name,
  N = atom_to_list(Mod_Name) ++ "." ++ atom_to_list(Fun_Name) ++ "." ++
  integer_to_list(Arity),

  Fixed_regs = fixed_registers(),
  Args1 = header_regs(Fixed_regs, []),
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
  RegList = lists:filter(fun reg_not_undef/1, Fixed_regs),
  I2 = load_regs(RegList),
  I3 = hipe_llvm:mk_br(mk_jump_label(1)),
  Final_Code = lists:flatten([I1,I2,ConstLoad,I3])++Code,
  [_|[_|Typ]] = lists:foldl(fun(X,Y) -> Y++", i64" end, [],
    Fixed_regs) ,
  Type = "{"++Typ++",i64"++"}",
  hipe_llvm:mk_fun_def([], [], "cc 11", [], Type, N,
                        Args1++Args2, [nounwind], [], Final_Code).

fixed_registers() ->
  case get(hipe_target_arch) of
    x86 -> [?HP, ?P, ?NSP];
    amd64 ->
      [?HP, ?P, ?NSP, ?FCALLS, ?HEAP_LIMIT];
    Other ->
      exit({?MODULE, map_registers, {"Unknown Architecture"}})
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
  I1 = hipe_llvm:mk_alloca("%"++R++"_var", "i64", [], []),
  I2 = hipe_llvm:mk_store("i64", "%"++R++"_in", "i64", "%"++R++"_var", [], [], false),
  load_regs(Rs, [I1,I2,Acc]).


%%-----------------------------------------------------------------------------
%%
%% Only For Testing
%%


%% Create Main Function (Only for testing reasons)

create_main(Dev, Name, Params) ->
  {_,N,_} = Name,
%  io:format(Dev, "@.str = private constant [3 x i8] c\"%d\\00\", align 1;",[]),
%  io:format(Dev, "~n~ndefine i64 @main() {~n", []),
%  io:format(Dev, "Entry:~n", []),
%  T1 = mk_temp(hipe_gensym:new_var(llvm)),
%  io:format(Dev, "~s = call {i64,i64,i64,i64,i64,i64} @~w(", [T1, N]),
%  init_params(Dev, 5+erlang:length(Params)),
%  io:format(Dev, ")~n", []),
%
%  io:format(Dev, "%0 = tail call i64 (i8*, ...)* @printf(i8* noalias " ++ 
%    "getelementptr inbounds ([3 x i8]* @.str, i64 0, i64 0)," ++ 
%    " i64 ~s) nounwind~n", [T1]),
%  io:format(Dev, "ret i64 ~s~n}~n",[T1]),
%  io:format(Dev, "declare i64 @printf(i8* noalias, ...) nounwind~n",[]),
  io:format(Dev, "declare {i64, i1} @llvm.smul.with.overflow.i64(i64 %a, "++
    "i64%b)~n", []),
  io:format(Dev, "declare {i64, i1} @llvm.ssub.with.overflow.i64(i64 %a, "++
    "i64%b)~n", []),
  io:format(Dev, "declare {i64, i1} @llvm.sadd.with.overflow.i64(i64 %a, "++
    "i64%b)~n", []),
io:format(Dev,"declare cc 11  {i64, i64, i64, i64, i64, i64} @bif_add(i64 %a, i64
  %b, i64 %c, i64 %d, i64 %e, i64 %q, i64 %l)~n",[]),
io:format(Dev,"declare cc 11  {i64, i64, i64, i64, i64, i64} @bif_sub(i64 %a, i64
  %b, i64 %c, i64 %d, i64 %e, i64 %q, i64 %l)~n",[]),
io:format(Dev,"declare cc 11  {i64, i64, i64, i64, i64, i64} @bif_mul(i64 %a, i64
  %b, i64 %c, i64 %d, i64 %e, i64 %q, i64 %l)~n",[]),
io:format(Dev,"declare cc 11  {i64, i64, i64, i64, i64, i64} @bif_div(i64 %a, i64
  %b, i64 %c, i64 %d, i64 %e, i64 %q, i64 %l)~n",[]).

%% Print random parameters in main function
init_params(Dev, 1) -> 
  io:format(Dev,"i64 ~w",[random:uniform(20)]);
init_params(Dev, N) -> 
  io:format(Dev,"i64 ~w,",[random:uniform(20)]),
  init_params(Dev, N-1).
