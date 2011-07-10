%% -*- erlang-indent-level: 2 -*-

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").
-include("hipe_llvm.hrl").
-include("../rtl/hipe_literals.hrl").
-export([translate/1,fix_closure_name/1]).

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
  %% To be used later
  IsClosure = hipe_rtl:rtl_is_closure(RTL),
  _IsLeaf = hipe_rtl:rtl_is_leaf(RTL),
%  io:format("Geia sou llvm!~n"),
  {Mod_Name, Fun_Name, Arity} = 
  case IsClosure of
    false ->
      Fun;
    true ->
      {M, Closure_Name, A} = Fun,
      {M, fix_closure_name(Closure_Name), A}
  end,
  %% Print RTL to file
  {ok, File_rtl} = file:open(atom_to_list(Fun_Name) ++ ".rtl", [write]),
  hipe_rtl:pp(File_rtl, RTL),
  file:close(File_rtl),
  %% Create NewData which containts also data for switches
  {NewData, SortedBy} = data_from_switches(Code, Data, []),
  %% Create constant map and write it to file for loader
  {ConstAlign,ConstSize,ConstMap,RefsFromConsts} =
  hipe_pack_constants:pack_constants([{Fun, [], NewData}], ?HIPE_X86_REGISTERS:alignment()),
  SC = hipe_pack_constants:llvm_slim_constmap(ConstMap),
  %% Extract constant labels from Constant Map (remove duplicates)
  ConstLabels = lists:usort(find_constants(SC)),
  %% io:format("--> RTL2LLVM: Constant Labels Found: ~w~n", [ConstLabels]),
  %% Extract atoms from RTL Code(remove duplicates)
  Atoms = lists:usort(find_atoms(Code)),
  %% io:format("--> RTL2LLVM Atoms Found ~w~n", [Atoms]),
  %% Create code to declare atoms
  AtomDecl = lists:map(fun declare_atom/1, Atoms),
  %% Create code to create local name for atoms
  AtomLoad = lists:map(fun load_atom/1, Atoms),
  %% Create code to declare constants 
  ConstDecl = lists:map(fun declare_constant/1, ConstLabels),
  %% Create code to create local name for constants
  ConstLoad = lists:map(fun load_constant/1, ConstLabels),
  %% Extract closures from RTL Code(remove duplicates)
  Closures = find_closures(Code),
  %% Create code to declare closures
  ClosureDecl = lists:map(fun declare_closure/1, Closures),
  %% Create code to create local name for closures
  ClosureLoad = lists:map(fun load_closure/1, Closures),
  %% Create LabelMap 
  TempLabelMap = lists:map(fun create_label_map/1, SortedBy),
  %% Collect gc roots
  %%GCRoots = collect_gc_roots(Code),
  %%GCRootDeclare = declare_gc_roots(GCRoots),
  Code2 = fix_invoke_calls(Code),
  LLVM_Code = translate_instr_list(Code2, []),
  LLVM_Code2 = create_header(Fun, Params, LLVM_Code,
    ClosureLoad++AtomLoad++ConstLoad,
    IsClosure),
  %% Find function calls in code
  Is_call = fun (X) -> is_external_call(X, atom_to_list(Mod_Name),
        atom_to_list(Fun_Name), integer_to_list(Arity)) end,
  I1 = lists:filter(fun is_call/1, LLVM_Code),
  I2 = lists:filter(Is_call, I1),
  %% Create code to declare external function
  Fun_Declarations = lists:map(fun call_to_decl/1, lists:filter(fun (X) ->
          string:substr(call_name(X),1,1) /= "%" end,  I2)),
  LLVM_Code3 = ClosureDecl++AtomDecl++ConstDecl++[LLVM_Code2|Fun_Declarations],
  CallDict = dict:new(),
  CallDict2 = lists:foldl(fun call_to_dict/2, CallDict, I1),
  CallDict3 = lists:foldl(fun const_to_dict/2, CallDict2, ConstLabels),
  CallDict4 = lists:foldl(fun atom_to_dict/2, CallDict3, Atoms),
  CallDict5 = labels_to_dict(TempLabelMap, CallDict4),
  %% Temporary Store inc_stack to Dictionary
  CallDict6 = dict:store("@inc_stack_0", {inc_stack_0}, CallDict5),
  CallDict7 = lists:foldl(fun closure_to_dict/2, CallDict6, Closures),
  {LLVM_Code3, CallDict7, SC, ConstAlign, ConstSize, TempLabelMap}.

%%-----------------------------------------------------------------------------

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
  Dict1 = dict:store("@.rodata"++integer_to_list(RodataNumber), {constant,
      ConstNumber}, Dict),
  labels_to_dict(Rest, Dict1, RodataNumber+1);
labels_to_dict([{ConstNumber, _, _, _}|Rest], Dict, RodataNumber) -> 
  Dict1 = dict:store("@.rodata"++integer_to_list(RodataNumber), {constant,
      ConstNumber}, Dict),
  labels_to_dict(Rest, Dict1, RodataNumber+1).

collect_gc_roots(Code) -> collect_gc_roots(Code, []).

collect_gc_roots([], Roots) -> Roots;
collect_gc_roots([I|Is], Roots) ->
  Dst = insn_dst(I),
  case Dst of 
    [] ->  collect_gc_roots(Is, Roots);
    _ -> 
      case hipe_rtl:is_var(Dst) of
        true -> collect_gc_roots(Is, [Dst|Roots]);
        false -> collect_gc_roots(Is, Roots)
      end
  end.

declare_gc_roots(Roots) -> declare_gc_roots(Roots, []).

declare_gc_roots([], Ins) -> Ins;
declare_gc_roots([Root|Rest], Ins) -> 
  GCRootName = trans_dst(Root) ++ "_gcroot",
  I1 = hipe_llvm:mk_alloca(GCRootName, "i64*", [], []),
  T1 = mk_temp(),
  I2 = hipe_llvm:mk_conversion(T1, bitcast, "i64**", GCRootName, "i8**"),
  I3 = hipe_llvm:mk_call([], false, [], [], void, "@llvm.gcroot", 
    [{"i8**",T1}, {"i8*", "null"}], []),
  declare_gc_roots(Rest, [I1, I2, I3 | Ins]).

%%----------------------------------------------------------------------------


%% Extract Closures from RTL CODE
find_closures(Code) -> find_closures(Code, []).
find_closures([], Closures) -> Closures;
find_closures([I|Is], Closures) ->
    case I of
      #load_address{} ->
        case hipe_rtl:load_address_type(I) of
          closure -> 
            Closure  = hipe_rtl:load_address_addr(I),
            find_closures(Is, [Closure | Closures]);
          _ -> find_closures(Is, Closures)
        end;
        _ -> find_closures(Is, Closures)
      end.

declare_closure({{_, ClosureName, _}, _, _})->
  FixedName = "@"++atom_to_list(fix_closure_name(ClosureName)),
  hipe_llvm:mk_const_decl(FixedName, "external constant", "i8", "").

load_closure({{_, ClosureName, _}, _, _})->
  FixedName = atom_to_list(fix_closure_name(ClosureName)),
  Dst = "%"++FixedName++"_var",
  Name = "@"++FixedName,
  hipe_llvm:mk_ptrtoint(Dst, "i8", Name, "i64").

closure_to_dict({{_, ClosureName, _}, _, _}=Closure, Dict)->
  FixedName = "@"++atom_to_list(fix_closure_name(ClosureName)),
  dict:store(FixedName, {closure, Closure}, Dict).

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
  LLVM_Name = make_llvm_id(atom_to_list(Atom)),
  Name = "@"++LLVM_Name,
  hipe_llvm:mk_const_decl(Name, "external constant", "i64", "").
load_atom(Atom) ->
  LLVM_Name = make_llvm_id(atom_to_list(Atom)),
  Dst = "%"++LLVM_Name++"_var",
  Name = "@"++LLVM_Name,
  hipe_llvm:mk_ptrtoint(Dst, "i64", Name, i64).
atom_to_dict(Atom, Dict) ->
  LLVM_Name = make_llvm_id(atom_to_list(Atom)),
  Name = "@"++LLVM_Name,
  dict:store(Name, {'atom', Atom}, Dict).

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
  Name = "@DL"++integer_to_list(Elem),
  dict:store(Name, {'constant', Elem}, Dict).

call_to_dict(Elem, Dict) -> 
  Name = case Elem of
    #llvm_call{} ->
      hipe_llvm:call_fnptrval(Elem);
    #llvm_invoke{} ->
      hipe_llvm:invoke_fnptrval(Elem)
  end,
  case re:run(Name, "@([a-zA-Z_0-9]*)\.([a-zA-Z_0-9]*)\.([a-zA-Z_0-9]*)",
      [global,{capture,all_but_first,list}]) of
    {match, [[BifName, [], []]]} -> 
      dict:store(Name, {erlang:list_to_atom(BifName)}, Dict);
    {match, [[M,F,A]]} -> 
      case M of
        "llvm" -> Dict;
        _ -> 
          dict:store(Name, {erlang:list_to_atom(M),
                        erlang:list_to_atom(F),
                        erlang:list_to_integer(A)}, Dict)
                end;
    {match, _} -> Dict;
    nomatch -> 
      case string:substr(Name,1,1) of
      "%" -> Dict;
          _ ->
      exit({?MODULE, call_to_dict, {"Unknown call",Name}})
  end
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
    #call{} -> case hipe_rtl:call_fun(I) of
        fwait -> io:format("Fwait found~n"),[];
        _ -> trans_call(I)
      end;
    #comment{} -> trans_comment(I);
    #enter{} -> trans_enter(I);
    #fconv{} -> trans_fconv(I);
    #fixnumop{} -> trans_fixnum(I);
    #fload{} -> trans_fload(I);
    #fmove{} -> trans_fmove(I);
    #fp{} -> trans_fp(I);
    #fp_unop{} -> trans_fp_unop(I);
    #fstore{} -> trans_fstore(I);
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
  [I5, I4, I3, I2, I1].
          
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
  T1 = mk_temp(),
  %% No Precoloured Registers can exit in an alu with overflow
  {Src1, []} =  trans_src(hipe_rtl:alub_src1(I)),
  {Src2, []} =  trans_src(hipe_rtl:alub_src2(I)),
  %% TODO: Fix call
  Name = case hipe_rtl:alub_op(I) of
          add -> "@llvm.sadd.with.overflow.i64";
          mul -> "@llvm.smul.with.overflow.i64";
          sub -> "@llvm.ssub.with.overflow.i64";
          Other -> exit({?MODULE, trans_alub_overflow, {"Unknown operator in
                  alu with overflow", Other}})
        end,
  I1 = hipe_llvm:mk_call(T1, false, [], [], "{i64, i1}", Name,
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
  [I4, I3, I2, I1].

trans_alub_no_overflow(I) ->
  %%alu
  T = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
    hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  I1 = trans_alu(T),
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
  [I6, I5, I2, I1].

%%
%% branch
%%
trans_branch(I) ->
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
  [I2, I1].


%%
%% call
%%
trans_call(I) ->
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
      ArgsInRegs++ lists:reverse(ArgsInStack)
  end,
  FixedRegs = fixed_registers(),
  {LoadedFixedRegs, I1} = load_call_regs(FixedRegs), 
  FinalArgs = fix_reg_args(LoadedFixedRegs) ++ ReversedArgs,
  {Name, I2} = case hipe_rtl:call_fun(I) of
    PrimOp when is_atom(PrimOp) -> {"@"++trans_prim_op(PrimOp), []};
    {M, F, A} when is_atom(M), is_atom(F), is_integer(A) ->
      {"@"++trans_mfa_name({M,F,A}), []};
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
          {TT2, [II2, II1]};
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
      CC -> trans_goto(hipe_rtl:mk_goto(CC))
    end,
    [I8, I7, I6, I3, I2, I1].

args_to_type(Args) -> 
  Args1 = lists:map(fun (_) -> "i64" end, Args),
  Args2 = lists:foldl(fun (A,B) -> A++","++B end, "", Args1),
  {Args3,_} =lists:split(erlang:length(Args2)-1, Args2),
  Args3.

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
  FinalArgs = fix_reg_args(LoadedFixedRegs) ++ ReversedArgs,
  {Name, I2} = case hipe_rtl:enter_fun(I) of
    PrimOp when is_atom(PrimOp) -> {"@"++trans_prim_op(PrimOp), []};
    {M, F, A} when is_atom(M), is_atom(F), is_integer(A) ->
      {"@"++trans_mfa_name({M,F,A}), []};
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
          {TT2, [II2, II1]};
        false -> exit({?MODULE, trans_call, {"Unimplemted Call to", Reg}}) 
      end
  end,
  %% TODO: Fix return type of calls
  T1 = mk_temp(),
  I3 = hipe_llvm:mk_call(T1, true, "cc 11", [], "{i64, i64, i64, i64}",
			 Name, FinalArgs, []),
  I4 = hipe_llvm:mk_ret([{"{i64,i64,i64,i64}", T1}]),
  [I4, I3, I2, I1].

%%
%% fconv
%%
trans_fconv(I) ->
  %% XXX: Can a fconv destination be a precoloured reg? 
  _Dst = hipe_rtl:fconv_dst(I),
  {Dst, []} = trans_dst(_Dst),
  _Src = hipe_rtl:fconv_src(I),
  {Src, I1} =  trans_float_src(_Src),
  I2 = hipe_llvm:mk_sitofp(Dst, "i64", Src, "double"),
  [I2, I1].
    
      
  
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


%% TODO: fload, fstore, fmove, and fp are almost the same with load,store,move
%% and alu. Maybe we should join them.

%%
%% fload
%% 
trans_fload(I) ->
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
  [I5, I4, I3, I2, I1].

%%
%% fmove
%%
trans_fmove(I) -> 
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
  [I3, I2, I1].

%%
%% fp
%%
trans_fp(I) ->
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
  [I6, I5, I4, I3, I2, I1].

%%
%% fp_unop
%%
trans_fp_unop(I) ->
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
  [I3, I2, I1].
%% TODO: Fix fp_unop in a way like the following. You must change trans_dest,
%% in order to call float_to_list in a case of float constant. Maybe the type
%% check is expensive...
% Dst = hipe_rtl:fp_unop_dst(I),
% Src = hipe_rtl:fp_unop_src(I),
% Op = hipe_rtl:fp_unop_op(I),
% Zero = hipe_rtl:mk_imm(0.0),
% I1 = hipe_rtl:mk_fp(Dst, Zero, Op, Src),
% trans_fp(I1).

%%
%% fstore
%%
trans_fstore(I) ->
  Base = hipe_rtl:fstore_base(I),
  I1 = case hipe_rtl_arch:is_precoloured(Base) of
    true -> trans_fstore_reg(I);
    false -> exit({?MODULE, trans_fstore ,{"Non Implemened yet", false}})
  end,
  I1.

trans_fstore_reg(I) ->
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
  [I4, I3, I2, I1].

%%
%% gctest
%%
trans_gctest(I) ->
  % For now ignore gc_test. Just print it as comment
  {W, []} = trans_src(hipe_rtl:gctest_words(I)),
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
  [Ins, I3, I2, I1].

%%
%% load_address
%%
trans_load_address(I) ->
  %% Check the load_type is constant. We have not implemented other cases yet.
  _Dst = hipe_rtl:load_address_dst(I),
  _Addr = hipe_rtl:load_address_addr(I),
  IsDstColoured = isPrecoloured(_Dst),
  {Dst, []} = case IsDstColoured of
    true -> {mk_temp(), []};
    false -> trans_dst(_Dst)
  end,
  Addr = case hipe_rtl:load_address_type(I) of
    constant -> "%DL"++integer_to_list(_Addr)++"_var";
    closure  -> 
      {Closure, _, _} = _Addr,
      {_, ClosureName, _} = Closure,
      "%"++atom_to_list(fix_closure_name(ClosureName))++"_var";
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
  [I2, I1].

%%
%% load_atom
%%
trans_load_atom(I) ->
  _Dst = hipe_rtl:load_atom_dst(I),
  _Atom = hipe_rtl:load_atom_atom(I),
  Atom_Name = "%"++make_llvm_id(atom_to_list(_Atom))++"_var",
  {Dst, []} = trans_dst(_Dst),
  hipe_llvm:mk_select(Dst, true, "i64", Atom_Name, "i64", "undef").

%%
%% move
%%
trans_move(I) ->
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
  [I3, I2, I1].

%% 
%% phi
%%
trans_phi(I) ->
  _Dst = hipe_rtl:phi_dst(I),
  {Dst, []} = trans_dst(_Dst),
  I1 = hipe_llvm:mk_phi(Dst , arg_type(_Dst), 
    trans_phi_list(hipe_rtl:phi_arglist(I))),
  I1.

trans_phi_list([]) -> [];
trans_phi_list([{Label, Value}| Args]) ->
  {Val, []} = trans_src(Value),
  [{Val, mk_jump_label(Label)} | trans_phi_list(Args)].

%%
%% return 
%%
%% TODO: Take care of returning many items
trans_return(I) ->
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
  I2 = hipe_llvm:mk_ret(Ret),
  [I2, I1].

%%
%% store 
%%
trans_store(I) ->
  Base = hipe_rtl:store_base(I),
  I1 = case hipe_rtl_arch:is_precoloured(Base) of
    true -> trans_store_reg(I);
    false -> trans_store_var(I)
  end,
  I1.

trans_store_var(I) ->
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
  [Ins, I2, I1].

trans_store_reg(I) ->
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
  [I5, I4, I3, I2, I1].

%%
%% switch
%%
trans_switch(I) ->
  _Src = hipe_rtl:switch_src(I),
  {Src, I1} = trans_src(_Src),
  LabelList = lists:map(fun mk_jump_label/1, hipe_rtl:switch_labels(I)),
  ValueList = lists:map(fun integer_to_list/1, lists:seq(0,
      length(LabelList)-1)),
  ValueLabelList = lists:zip(ValueList, LabelList),
  I2 = hipe_llvm:mk_switch("i64", Src, lists:nth(length(LabelList)-1, LabelList), ValueLabelList),
  [I2, I1]. 
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

is_call(I) -> 
  case I of 
    #llvm_call{} -> true;
    #llvm_invoke{} -> true;
    _ -> false
  end.

call_name(I) ->
  case I of 
    #llvm_call{} ->
      hipe_llvm:call_fnptrval(I);
    #llvm_invoke{} ->
      hipe_llvm:invoke_fnptrval(I);
    Other -> exit({?MODULE, call_name, {"Not a call", Other}})
  end.

is_external_call(I, M, F, A) -> 
  case I of
    #llvm_call{} -> 
      Name = hipe_llvm:call_fnptrval(I),
      case re:run(Name, "@([a-z_0-9]*)\.([a-z_0-9]*)\.([a-z_0-9]*)",
          [global,{capture,all_but_first,list}]) of
        {match, [[M,F,A]]} -> 
          false;
        _ -> true
      end;
    #llvm_invoke{} -> 
      Name = hipe_llvm:invoke_fnptrval(I),
      case re:run(Name, "@([a-z_0-9]*)\.([a-z_0-9]*)\.([a-z_0-9]*)",
          [global,{capture,all_but_first,list}]) of
        {match, [[M,F,A]]} -> 
          false;
        _ -> true
      end;
    _ -> false
  end.

call_to_decl(A) -> 
  case A of
    #llvm_call{} ->
      Cconv = hipe_llvm:call_cconv(A),
      Type = hipe_llvm:call_type(A),
      Name = hipe_llvm:call_fnptrval(A),
      Args = hipe_llvm:call_arglist(A);
    #llvm_invoke{} ->
      Cconv = hipe_llvm:invoke_cconv(A),
      Type = hipe_llvm:invoke_type(A),
      Name = hipe_llvm:invoke_fnptrval(A),
      Args = hipe_llvm:invoke_arglist(A)
  end,
  Args_type = lists:map(fun({X,_}) -> X end, Args),
    hipe_llvm:mk_fun_decl([], [], Cconv, [], Type, Name, Args_type, []). 


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
  

insn_dst(I) ->
  case I of
    #alu{} -> hipe_rtl:alu_dst(I);
    #alub{} -> hipe_rtl:alub_dst(I);
    #call{} -> 
      case hipe_rtl:call_dstlist(I) of
        [] -> [];
        [_, _ |[]] -> exit({?MODULE, insn_dst, {"Call destination list
                      not implemented yet", hipe_rtl:call_dstlist(I)}});
        [Dst] -> Dst
      end;
    #load{} -> hipe_rtl:load_dst(I);
    #load_address{} -> hipe_rtl:load_address_dst(I);
    #load_atom{} -> hipe_rtl:load_atom_dst(I);
    %#load_word_index{} -> ok;
    #move{} -> hipe_rtl:move_dst(I);
    %#multimove{} -> ok;
    #phi{} -> hipe_rtl:phi_dst(I);
    %#switch{} -> hipe_rtl:switch(I);
    _ -> []
  end.

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

%% Create Header for Function 

create_header(Name, Params, Code, ConstLoad, IsClosure) ->
  % TODO: What if arguments more than available registers?
  % TODO: Jump to correct label
  {Mod_Name,FN,Arity} = Name,
  Fun_Name = case IsClosure of 
    true -> fix_closure_name(FN);
    false -> FN
  end,
  N = atom_to_list(Mod_Name) ++ "." ++ atom_to_list(Fun_Name) ++ "." ++
  integer_to_list(Arity),

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
  I3 = hipe_llvm:mk_br(mk_jump_label(1)),
  Final_Code = lists:flatten([I1,Exception_Sync,I2,ConstLoad,I3])++Code,
  [_|[_|Typ]] = lists:foldl(fun(_,Y) -> Y++", i64" end, [],
    Fixed_regs) ,
  Type = "{"++Typ++",i64"++"}",
  hipe_llvm:mk_fun_def([], [], "cc 11", [], Type, N,
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
