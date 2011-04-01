-module(tuple_test).
-export([mk_tuple/2, 
        mk_tuple/3, 
        mk_nested_tuple/3]).

-spec mk_tuple(A, B) -> {A, B}.
mk_tuple(X, Y) ->
    {X, Y}.

-spec mk_tuple(A, B, C) -> {A, B, C}.
mk_tuple(X, Y, Z) ->
    {X, Y, Z}.

-spec mk_nested_tuple(A, B, C) -> {A, {B, C}}.
mk_nested_tuple(X, Y, Z) ->
    {X, {Y, Z}}.
