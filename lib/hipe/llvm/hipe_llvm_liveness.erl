-module(hipe_llvm_liveness).

-export([analyze/2]).

-include("../rtl/hipe_rtl.hrl").

%% @doc Find gc roots and explicitly mark when they go out of scope, based
%% on the liveness analyzis performed by the hipe_rtl_liveness:analyze/1.
%% Also minimize the stack usage that is resulting from LLVM gc root support,
%% by mapping idependent variables to the same stack slot.
analyze(RTL, RtlCfg) ->
  %% Get Liveness Analysis from HiPE
  Liveness = hipe_rtl_liveness:analyze(RtlCfg),
  %% hipe_rtl_liveness:pp(RtlCfg),
  RtlCode = hipe_rtl:rtl_code(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  %% hipe_rtl:pp(RtlLinear),
  %% Store the code in an ordered dictionary, with keys being the
  %% numbering of instructions
  RtlDict = rtl_to_dict(RtlCode, orddict:new(), 0),
  %% For each variable, identify the intervals to which the variable is live
  Intervals = find_live_intervals(RtlDict, Liveness),
  %% erlang:display(Intervals),
  %% Find the indexing of RTL call instructions
  CallIndexes = find_call_indexes(RtlDict, 0, []),
  %% erlang:display(CallIndexes),
  Roots = find_roots(CallIndexes, Intervals, []),
  %% erlang:display(Roots),
  %% We are only interested for GC roots live intervals
  RootIntervals = dict:filter(fun (Key, _Val) -> lists:member(Key, Roots) end,
                              Intervals),
  %% erlang:display(RootIntervals),
  %% Minimize the stack usage by identifying roots that have no overlapping
  %% live intervals
  StackMap = minimize_stack_usage(Roots, RootIntervals, []),
  %% map_to_slots(StackMap1, 0, []).
  %% erlang:display(StackMap),
  %% Change RTL code in order to use the minimized variables-roots.
  %% For example if StackMap contains an entry of the form {19,[20,21]}
  %% all uses of v20 and v21 will be replaced with v19
  RtlCode2 = update_rtl(StackMap, RtlCode),
  %% Create again a dictionary. In order to mark when the new roots go out
  %% of scope.
  RtlDict2 = rtl_to_dict(RtlCode2, orddict:new(), 0),
  %% Live intervals for the minimized roots
  RootIntervals2 = update_root_intervals(StackMap, RootIntervals),
  %%
  RtlDict3 = kill_dead_vars(RtlDict2, RootIntervals2),
  {_, FinalCode} = lists:unzip(orddict:to_list(RtlDict3)),
  %% Update the RTL
  RTL2 = hipe_rtl:rtl_code_update(RTL, FinalCode),
  NewParams = update_params(StackMap, Params),
  %% erlang:display(NewParams),
  FinalRTL = hipe_rtl:rtl_params_update(RTL2, NewParams),
  %% Return the new Roots
  MinimizedRoots = [Root || {Root, _} <-StackMap],
  {FinalRTL, MinimizedRoots}.


%%----------------------------------------------------------------------------
find_live_intervals(RtlDict, Liveness) ->
  Intervals = find_live_intervals(RtlDict, Liveness, [], 0, [], dict:new()),
  dict:map(fun normalize_intervals/2, Intervals).

find_live_intervals(RtlDict, Liveness, LiveOut, Number, BBRest, Intervals) ->
  case orddict:find(Number, RtlDict) of
    {ok, I} ->
      case I of
        #label{} ->
          Label = hipe_rtl:label_name(I),
          %% Close all live intervals, concering previous BB
          Intervals2 = close_all_intervals(Intervals, Number),
          %% LiveIn variables of the BB
          NewLiveIn = strip(hipe_rtl_liveness:livein(Liveness, Label)),
          %% Open all live intervals for this BB live in variables
          Intervals3 = open_intervals(NewLiveIn, Intervals2, Number),
          %% LiveOut variables of BB
          NewLiveOut = strip(hipe_rtl_liveness:liveout(Liveness, Label)),
          %% Find all the instructions that are included in this BB
          BBIns = find_bb_ins(RtlDict, Number+1, []),
          find_live_intervals(RtlDict, Liveness, NewLiveOut, Number+1,
                              BBIns, Intervals3);
        Ins ->
          %% Variables that are defined by this instruction
          Defines = lists:usort(strip(hipe_rtl:defines(Ins))),
          Intervals2 = open_intervals(Defines, Intervals, Number),
          %% Variables that are used by this instruction
          Uses = lists:usort(strip(hipe_rtl:uses(Ins))),
          %% The rest instruction of this BB
          BBRest2 = safe_tail(BBRest),
          %% Variables that are used and defined after this instruction in this BB
          UsedAfter = lists:usort(strip(lists:flatten(
                                 [hipe_rtl:uses(V) || V <- BBRest2]))),
          %% DefinedAfter = lists:usort(strip(lists:flatten(
          %%                            [hipe_rtl:defines(V) || V <- BBRest2]))),
          %%XXX: Defined after!!
          %% Close intervals for variables that are not used again in this BB
          %% and that do not belong to LiveOut
          %%XXX:Search and optimize this!!
          Intervals3 = close_intervals(Uses, Intervals2,
                                       lists:usort(UsedAfter++LiveOut), Number),
          find_live_intervals(RtlDict, Liveness, LiveOut, Number+1, BBRest2,
                              Intervals3)
      end;
    _ ->
      %% Code end.
      close_all_intervals(Intervals, Number-1)
  end.

%%-----------------------------------------------------------------------------
%% Open the intervals for the specified list of variables. An open interval has
%% the form: (StartIndex, -1)
open_intervals([], Intervals, _) -> Intervals;
open_intervals([V|Vs], Intervals, Number) ->
  case dict:find(V, Intervals) of
    {ok, VI} -> %% Redefined variable
      case has_open_interval(VI) of
        true -> %% Redefined and live. Just ignore it
          open_intervals(Vs, Intervals, Number);
        false ->
          Intervals2 = dict:store(V, [{Number, -1}|VI], Intervals),
          open_intervals(Vs, Intervals2, Number)
      end;
    error -> %% New Variable
      Intervals2 = dict:store(V, [{Number, -1}], Intervals),
      open_intervals(Vs, Intervals2, Number)
  end.

has_open_interval([{_, -1}|_]) -> true;
has_open_interval(_) -> false.

%% Close intervals for all variables in the dictionary
close_all_intervals(Intervals, Number) ->
  Vars = dict:fetch_keys(Intervals),
  close_intervals(Vars, Intervals, [], Number).

%% Close the intervals for the specified list of variables ONLY if
%% the variable does not belong to the UsedAfter list. Number specifies
%% the end of the interval.
close_intervals(Variables, Intervals, UsedAfter, Number) ->
  close_intervals(Variables--UsedAfter, Intervals, Number).

close_intervals([], Intervals,  _) -> Intervals;
close_intervals([V|Vs], Intervals, Number) ->
  case dict:find(V, Intervals) of
    {ok, VI} ->
      VI2 = close_interval(VI, Number),
      Intervals2 = dict:store(V, VI2, Intervals),
      close_intervals(Vs, Intervals2, Number);
    _ ->
      error({hipe_llvm_livenes, close_intervals, "Can not close a not
            open interval"})
   end.

close_interval([{Start, -1}|Rest], Number) -> [{Start, Number}|Rest];
close_interval(X, _) -> X.


find_call_indexes(RtlDict, Number, CallIndexes) ->
  case orddict:find(Number, RtlDict) of
    {ok, I} ->
      case hipe_rtl:is_call(I) of
        true -> find_call_indexes(RtlDict, Number+1, [Number|CallIndexes]);
        false -> find_call_indexes(RtlDict, Number+1, CallIndexes)
      end;
    _ ->
      %% Costs a lot! Do it better!
      CallIndexes
  end.


%% Normalize intervals. Opening a closing intervals around labels, produces
%% intervals of the form [(a,b),(b,c)]. We just convert them to (a,c).
normalize_intervals(_Var, Intervals) ->
  Intervals2 = lists:reverse(Intervals),
  do_normalize(Intervals2).

do_normalize([]) -> [];
do_normalize([{Start1, Stop1}, {Start2, Stop2}|Rest]) when Stop1 == Start2 ->
  do_normalize([{Start1, Stop2}|Rest]);
do_normalize([Interval|Rest]) ->
  [Interval|do_normalize(Rest)].

%%-----------------------------------------------------------------------------
%% GC Roots are those variable that are live when a call happens(Calls are the
%% safe points). So we identify the GC roots, by checking if a call number is
%% contained to a variables live interval.
find_roots([], _, Roots) -> lists:usort(Roots);
find_roots([N|Ns], Intervals, Roots) ->
  Roots1 = find_roots_for_call(N, Intervals),
  find_roots(Ns, Intervals, Roots1 ++ Roots).

find_roots_for_call(N, Intervals) ->
  RootsDict = dict:filter(fun(_Key, Val) -> number_belongs_to_intervals(N, Val)
                          end, Intervals),
  dict:fetch_keys(RootsDict).

number_belongs_to_intervals(_N, []) -> false;
number_belongs_to_intervals(N, [{Start,Stop}|_Rest])
    when Start<N andalso N < Stop -> true;
number_belongs_to_intervals(N, [_| Rest]) -> number_belongs_to_intervals(N, Rest).

%%-----------------------------------------------------------------------------
%% Minimize the stack usage by identifying roots that have no overlapping
%% live intervals. Since two variables are never live together they can be
%% mapped to the same variable, which will be marked to the LLVM as a stack
%% containing a gc root.
minimize_stack_usage([], _, StackMap) -> StackMap;
minimize_stack_usage([R|Rs], RootsInterval, StackMap) ->
  %% Find the live intervals for root R
  {ok, Intervals1} = dict:find(R, RootsInterval),
  IndendentRoots = find_indepent_roots(Intervals1, Rs, RootsInterval, []),
  RestRoots = Rs -- IndendentRoots,
  minimize_stack_usage(RestRoots, RootsInterval, [{R, IndendentRoots}|StackMap]).

find_indepent_roots(_, [], _, IRoots) ->
  IRoots;
find_indepent_roots(Intervals, [R|Rs], RootsInterval, IRoots) ->
  {ok, Intervals2} = dict:find(R, RootsInterval),
  case intervals_conlict(Intervals, Intervals2) of
    true ->
      find_indepent_roots(Intervals, Rs, RootsInterval, IRoots);
    false ->
      %% The new live intervals is the join of the live intervals
      %% of the indepent roots
      MergedIntervals = lists:keymerge(1, Intervals, Intervals2),
      find_indepent_roots(MergedIntervals, Rs, RootsInterval, [R|IRoots])
  end.

%% Naive checking about if the intervals are overlapping!
%% TODO: Optimize this process
intervals_conlict(Interval1, Interval2) ->
  lists:any(fun (X) -> conflicts(X, Interval2) end, Interval1).

conflicts(_, []) -> false;
conflicts({_S1,E1}=A, [{S2,_E2}|Rest]) when E1 =< S2 -> conflicts(A,Rest);
conflicts({S1,_E1}=A, [{_S2,E2}|Rest]) when S1 >= E2 -> conflicts(A,Rest);
conflicts({S1,E1}=A, [{S2, E2}|Rest]) ->
  S2=<S1 andalso S1 =< E2 orelse %% S2<=S1<=E2
  S2=<E1 andalso E1 =< E2 orelse %% S2<=E1<=E2
  S1=<S2 andalso E1 >= E2 orelse %% S1<=S2<=E2<=E1
  S2=<S1 andalso E2 >= E1 orelse %% S2<=S1<=E1<=E2
  conflicts(A, Rest).


%% map_to_slots([], _Number, Acc) -> lists:reverse(Acc);
%% map_to_slots([ {V,Vs} | Rest], Number, Acc) ->
%%   map_to_slots(Rest, Number+1, [{Number, [V|Vs]}|Acc]).


%%----------------------------------------------------------------------------
update_rtl([], RtlCode) -> RtlCode;
update_rtl([{Root, MappedRoots}|Rest], RtlCode) ->
  MapToVar = hipe_rtl:mk_var(Root),
  Subst = [ {hipe_rtl:mk_var(Var), MapToVar} || Var <- MappedRoots],
  %% io:format("Substitution is :~w~n",[Subst]),
  %% Substiture used and definitions of the mapped roots
  RtlCode1 = [hipe_rtl:subst_uses(Subst, I) || I<-RtlCode],
  RtlCode2 = [hipe_rtl:subst_defines(Subst, I) || I<-RtlCode1],
  update_rtl(Rest, RtlCode2).

update_params([], Params) -> Params;
update_params([{Root, Vars}|Rest], Params) ->
  MapToVar = hipe_rtl:mk_var(Root),
  Subst = [{hipe_rtl:mk_var(Var), MapToVar} || Var <- Vars],
  %% io:format("Params: Substitution is: ~w~n",[Subst]),
  Params2 = hipe_rtl:subst_list(Subst, Params),
  update_params(Rest, Params2).

update_root_intervals([], RootIntervals) ->
  dict:map(fun normalize_intervals/2, RootIntervals);
update_root_intervals([{R,Rs}|Rest], RootIntervals) ->
  RootsI2 = dict:store(R, [], RootIntervals),
  RootsI3 = do_update_intervals(Rs, R, RootsI2),
  update_root_intervals(Rest, RootsI3).

do_update_intervals([], _, Roots) -> Roots;
do_update_intervals([V|Vs], S, Roots) ->
  Interval = dict:fetch(V, Roots),
  Roots1 = dict:erase(V, Roots),
  Int2 = dict:fetch(S, Roots1),
  Root2 = dict:store(S, Interval++Int2, Roots1),
  do_update_intervals(Vs, S ,Root2).


kill_dead_vars(RtlDict, RootIntervals) ->
  Intervals = dict:to_list(RootIntervals),
  kill_dead_vars2(Intervals, RtlDict).

kill_dead_vars2([], RtlDict) -> RtlDict;
kill_dead_vars2([{Var, Intervals}|Rest], RtlDict) ->
  RtlDict2 = kill_dead_var(Intervals, Var, RtlDict),
  kill_dead_vars2(Rest, RtlDict2).

kill_dead_var([], _, RtlDict) -> RtlDict;
kill_dead_var([{_Start, Stop}|Rest], Var, RtlDict) ->
  OldVar = hipe_rtl:mk_var(Var),
  DeadVar = kill_var(OldVar),
  {ok, OldIns} = orddict:find(Stop, RtlDict),
  NewIns = hipe_rtl:subst_uses_llvm([{OldVar,DeadVar}], OldIns),
  RtlDict2 = orddict:store(Stop, NewIns, RtlDict),
  kill_dead_var(Rest, Var, RtlDict2).


%%----------------------------------------------------------------------------
%% @doc Convert a list of elements, to a an ordered dictionary
%%      with keys the numbering of elements.
rtl_to_dict([], RtlDict, _) -> RtlDict;
rtl_to_dict([I|Is], RtlDict, Number) ->
  RtlDict2 = orddict:store(Number, I, RtlDict),
  rtl_to_dict(Is, RtlDict2, Number+1).

safe_tail([]) -> [];
safe_tail([_|Xs]) -> Xs.

find_bb_ins(RtlDict, Number, Acc) ->
  case orddict:find(Number, RtlDict) of
    {ok, I} ->
      case I of
        #label{} -> lists:reverse(Acc);
        _ -> find_bb_ins(RtlDict, Number+1, [I|Acc])
      end;
    _ ->
      lists:reverse(Acc)
  end.

%% Update the liveness of a var,in order to mark that this is the last use.
kill_var(Var) -> hipe_rtl:var_liveness_update(Var, dead).

%% We are only interested for rtl_vars, since only rtl_vars are possible gc
%% roots.
strip(L) -> [Y || {rtl_var, Y, _} <- L].
