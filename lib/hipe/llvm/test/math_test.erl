-module(math_test).
-export([
	 inc/1, dec/1, 
	 mul/2, mydiv/2,
	 add42/1
	]).

-spec inc(Integer) -> Integer.
inc(X) ->
    X+1.

-spec dec(Integer) -> Integer.
dec(X) ->
    X-1.

-spec mul(Integer, Integer) -> Integer.
mul(X, Y) ->
    X*Y.

-spec mydiv(Integer, Integer) -> Integer.
mydiv(X, Y) ->
    X div Y.

-spec add42(float()) -> float().
add42(X) ->
    X+42/2+21.
