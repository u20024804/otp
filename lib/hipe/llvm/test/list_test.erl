-module(list_test).
-export([alist/2, nested_list/3,big_list/10,weird_list/4]).

alist(X,Y) -> [X,Y].

nested_list(X,Y,Z) -> [X, [Y,Z]].

big_list(A, B, C, D, E, F, X, Y, Z, W) -> [A, B, C, D, E, F, X, Y, Z, W].

weird_list(X,Y,Z,W) -> [{X}, [Y, [{Z,W}]]].
