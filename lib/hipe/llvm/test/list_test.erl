-module(list_test).
-compile(export_all).

alist() -> [1,2,3,4,5,[5,6]].

alist(X) -> [1,2,3,4,5,6,7]++X++[1,2,3].

alist(X,Y) -> [X,Y].

alist(X,Y,Z) -> listsX++lists:reverse(Y)++Z.

nested_list(X,Y,Z) -> [X, [Y,Z]].

big_list(A, B, C, D, E, F, X, Y, Z, W) -> [A, B, C, D, E, F, X, Y, Z, W].

weird_list(X,Y,Z,W) -> [{X}, [Y, [{Z,W}]]].
