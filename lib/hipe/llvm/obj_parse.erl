%% Temporary Module for parsing object file produced by LLVM.
%% 
%% Object file is parsed in order to extract relocations entries, needed
%% by the hipe_unified_loader.erl
%%
%% For now we use objdump(binutils) to display relocations entries and extract them
%% with awk script and regular expressions. 

-module(obj_parse).
-export([get_relocs/1]).

%% flatten_call_list/1
flatten_call_list(L) ->
  L1 = lists:keysort(1,L),
  L2 = lists:foldl(fun (Li,Acc) -> flatten_call_list(Li, Acc) end, [], L1),
  L2.

%% floatten_call_list/2
flatten_call_list({Fun, Off}, []) ->
  [{Fun, [Off]}];
flatten_call_list({Fun, Off}, [{PrevFun,Offs} | T]) ->
  case Fun == PrevFun of
    true ->
      [{PrevFun, [Off|Offs]} | T];
    false ->
      [{Fun, [Off]}, {PrevFun, Offs} | T]
  end.

%% Takes a Hex number in a string and converts it in (integer) decimal.
hex_to_dec(StrN) ->
    {ok, [Num], _} = io_lib:fread("~16u", StrN),
    Num.

get_relocs(ObjFile) ->
  S = os:cmd("objdump -r " ++ ObjFile ++ " | awk 'NR>5 && NF>0{print \"_\"$1\"_\" \" \" \"{\"$3\"}\"}' "),
  Options = [global, {capture, all_but_first, list}],
  MatchedRelocs = 
  case re:run(S, "_([0-9a-f]*)_ {([a-z]*_[a-z]*)", Options) of
    {match, ListOfMatches} -> 
      ListOfMatches;
    nomatch -> 
      []
  end ,   
  io:format("Get_Relocs: ~w", [MatchedRelocs]),
  %% Transform match list of form: [["000000000057", "addd"], ["0000000042", "foo"]]
  %% to form: [{"addd", hex("57")}, {"foo", hex("42")}]
  Relocs = [ {Fun, hex_to_dec(HexOff)} || [HexOff, Fun] <- MatchedRelocs ],
  FlattenedRelocs = flatten_call_list(Relocs),
  FlattenedRelocs1 = lists:map(fun({A,B}) -> {map_bifs(A),B} end, FlattenedRelocs),
  FinalRelocs = [{3, FlattenedRelocs1}],
  FinalRelocs.

map_bifs(Name) ->
  case Name of
    "bif_add" -> '+';
    "bif_sub" -> '-';
    "bif_mul" -> '*';
    "bif_div" -> 'div'
  end.
