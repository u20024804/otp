-module(hipe_llvm_liveness).

-export([analyze/1]).

%% @doc Find gc roots and explicitly mark when they go out of scope, based
%% on the liveness analyzis performed by the hipe_rtl_liveness:analyze/1.
analyze(RtlCfg) ->
  Live = hipe_rtl_liveness:analyze(RtlCfg),
  %% hipe_rtl_liveness:pp(RtlCfg),
  NewRtlCfg = annotate_dead_vars(RtlCfg, Live),
  Roots = find_roots(RtlCfg, Live),
  {NewRtlCfg, Roots}.

%% @doc This function is responsible for marking when RTL variables (rtl_var)
%% go out of scope (dead), based on the liveness analysis performed in RTL.
%% This pass is needed for the LLVM back end because the LLVM framework
%% forces us to explicit mark when gc roots are no longer live (RTL vars
%% are the possible gc roots).
annotate_dead_vars(CFG, Liveness) ->
  Labels = hipe_rtl_cfg:postorder(CFG),
  annotate_dead_vars_bb(Labels, CFG, Liveness).

%% Marking dead variables in a basic block. Which variables we need to mark as
%% dead in each basic block ? The last use of each variable for which one of
%% two following applies:
%% (1) Is live on entry to the block(livein list) and not on exit(liveout list)
%% (2) Belongs neither to livein or liveout, but is initiated in the basic block
%% and its last use is also in the basic block.
annotate_dead_vars_bb([], CFG, _Liveness) ->
  CFG;
annotate_dead_vars_bb([L|Ls], CFG, Liveness)  ->
  BB = hipe_rtl_cfg:bb(CFG, L),
  Code0 = hipe_bb:code(BB),
  LiveIn = strip(hipe_rtl_liveness:livein(Liveness, L)),
  LiveOut = strip(hipe_rtl_liveness:liveout(Liveness, L)),
  %% InternalDead are the variables for which (2) rule applies
  InternalDead = find_dead_in_block(Code0, LiveOut),
  NewCode = annotate_in_bb(Code0, (LiveIn--LiveOut)++InternalDead),
  NewBB = hipe_bb:code_update(BB, NewCode),
  NewCFG = hipe_rtl_cfg:bb_add(CFG, L, NewBB),
  annotate_dead_vars_bb(Ls, NewCFG, Liveness).

%% We are only interested for rtl_vars, since only rtl_vars are possible gc
%% roots.
strip([]) -> [];
strip([{rtl_var, Y, _}|Xs]) ->
  [Y | strip(Xs)];
strip([_|Xs]) ->
   strip(Xs).

%% RTL variables that are initiated in the basic block and their last
%% use is also in the basic block, i.e they do not belong to the liveout list.
find_dead_in_block(Code, LiveOut) ->
  Defines = lists:map(fun hipe_rtl:defines/1, Code),
  Defines2 = lists:flatten(Defines),
  %% The list of defines(variables that are being defined in a block) must not have
  %% duplicate elements!
  Defines3 = lists:usort(strip(Defines2)),
  lists:subtract(Defines3, LiveOut).

annotate_in_bb(Code, DeadVars) ->
  annotate_in_bb(lists:reverse(Code), DeadVars, []).

annotate_in_bb([], _DeadVars, NewCode) ->
  NewCode;

annotate_in_bb([I|Is], DeadVars, CodeAcc) ->
  {NewI, RestDeadVars} = annotate_in_ins(I, DeadVars),
  annotate_in_bb(Is, RestDeadVars, [NewI|CodeAcc]).

annotate_in_ins(I, []) -> {I, []};
annotate_in_ins(I, Deads) ->
 Uses = hipe_rtl:uses(I),
 VarUses = lists:filter(fun hipe_rtl:is_var/1, Uses),
 _Indexes = lists:map(fun hipe_rtl:var_index/1, VarUses),
 %% Indexes of all variables used in an instruction
 Indexes = lists:usort(_Indexes),
 %% CommonIndexes are indexes that belong to the dead variables
 CommonIndexes = find_common(Indexes, Deads),
 %% A variable can go out of scope only one time in a basic block.
 %% So we remove the dead ones to avoid extra checks.
 RestDeads = lists:subtract(Deads, CommonIndexes),
 OldVars = lists:map(fun hipe_rtl:mk_var/1, CommonIndexes),
 NewVars = lists:map(fun kill_var/1, OldVars),
 %% Create a list with the substitution of the old vars with the new
 %% ones which are marked with the dead keyword
 Subtitution = lists:zip(OldVars, NewVars),
 {hipe_rtl:subst_uses_llvm(Subtitution, I), RestDeads}.

%% Update the liveness of a var,in order to mark that this is the last use.
kill_var(Var) ->
  hipe_rtl:var_liveness_update(Var, dead).

%% Find the common elements of two lists
find_common(List1, List2) ->
  Different = lists:subtract(List2, List1),
  lists:subtract(List2, Different).

%% @doc Finds all possible roots of a function. Possible roots are all
%% RTL variables (rtl_var). However, since safe points are function calls, we
%% consider as possible gc roots only RTL variables that are live around
%% function calls.
find_roots(CFG, Liveness) ->
  %% Parameters of the function are variables and thus possible gc roots
  Params = strip(hipe_rtl_cfg:params(CFG)),
  Labels = hipe_rtl_cfg:postorder(CFG),
  Roots0 = lists:map(fun (X) -> find_roots_bb(X, CFG, Liveness) end, Labels),
  lists:usort(lists:flatten(Roots0)++Params).

find_roots_bb(L, CFG, Liveness)  ->
  BB = hipe_rtl_cfg:bb(CFG, L),
  Code = hipe_bb:code(BB),
  case has_sp(Code) of
    true ->
      LiveIn = strip(hipe_rtl_liveness:livein(Liveness, L)),
      LiveOut = strip(hipe_rtl_liveness:liveout(Liveness, L)),
      Internal = find_dead_in_block(Code, LiveOut),
      LiveIn++LiveOut++Internal;
    false ->
      []
  end.

%% Tests whether a list of instructions(basic block instructions) has
%% a safe point, ie a function call.
has_sp(Code) ->
  Calls = lists:filter(fun hipe_rtl:is_call/1, Code),
  length(Calls)>0.
