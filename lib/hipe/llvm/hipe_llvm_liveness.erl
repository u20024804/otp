-module(hipe_llvm_liveness).

-include("../flow/cfg.hrl").
-include("../rtl/hipe_rtl.hrl").
-export([annotate_dead_vars/2, find_roots/2]).

annotate_dead_vars(CFG, Liveness) ->
  Labels = hipe_rtl_cfg:postorder(CFG),
  annotate_dead_vars_bb(Labels, CFG, Liveness).

annotate_dead_vars_bb([], CFG, _Liveness) ->
  CFG;
annotate_dead_vars_bb([L|Ls], CFG, Liveness)  ->
  BB = hipe_rtl_cfg:bb(CFG, L),
  Code0 = hipe_bb:code(BB),
  LiveIn = strip(hipe_rtl_liveness:livein(Liveness, L)),
  LiveOut = strip(hipe_rtl_liveness:liveout(Liveness, L)),
  InternalDead = find_dead_in_block(Code0, LiveOut),
  Code = annotate_in_bb(Code0, (LiveIn--LiveOut)++InternalDead),
  NewBB = hipe_bb:code_update(BB, Code),
  NewCFG = hipe_rtl_cfg:bb_add(CFG, L, NewBB),
  annotate_dead_vars_bb(Ls, NewCFG, Liveness).

strip([]) ->
   [];
 strip([{rtl_var, Y, _}|Xs]) ->
   [Y|strip(Xs)];
strip([{rtl_reg, _, _}|Xs]) ->
   strip(Xs);
strip([{_, _}|Xs]) ->
   strip(Xs).%

find_dead_in_block(Code, LiveOut) ->
  Defines = lists:map(fun hipe_rtl:defines/1, Code),
  Defines2 = lists:flatten(Defines),
  Defines3 = strip(Defines2),
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
 Indexes = lists:usort(_Indexes),
 CommonIndexes = find_common(Indexes, Deads),
 RestDeads = lists:subtract(Deads, CommonIndexes),
 OldVars = lists:map(fun hipe_rtl:mk_var/1, CommonIndexes),
 NewVars = lists:map(fun kill_var/1, CommonIndexes),
 Subtitution = lists:zip(OldVars, NewVars),
 {hipe_rtl:subst_uses_llvm(Subtitution, I), RestDeads}.

kill_var(Index) ->
  hipe_rtl:mk_var(Index, dead).

find_common(Indexes, Deads) ->
  find_common(Indexes, Deads, []).
find_common([], _Deads, Acc) ->
  Acc;
find_common([I|Is], Deads, Acc) ->
  case lists:member(I, Deads) of
    true -> find_common(Is, Deads, [I|Acc]);
    false -> find_common(Is, Deads, Acc)
  end.

%% Finds all possible roots of a function
find_roots(CFG, Liveness) ->
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

%% Tests whether a function has a safe point
has_sp(Code) ->
  Calls = lists:filter(fun hipe_rtl:is_call/1, Code),
  length(Calls)>0.

