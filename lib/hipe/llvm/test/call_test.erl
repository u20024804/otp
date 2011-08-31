-module(call_test).
-compile(export_all).

factorial(0) -> 1;
factorial(1) -> 1;
factorial(X) ->
  X*factorial(X-1).

sum(1) -> 1;
sum(X) -> X+sum(X-1).


plusplus(X) -> 
  A = math_test:inc(X),
  math_test:inc(A).

fib(0) -> 0;
fib(1) -> 1;
fib(X) -> fib(X-1)+fib(X-2).
test3(X) ->
  case X of
    a -> 0;
    aa -> 1;
    aab -> 2;
    aabc -> 3;
    aabcd -> 4;
    ba -> 0;
    baa -> 1;
    baab -> 2;
    baabc -> 3;
    baabcd -> 4;
    ca -> 0;
    caa -> 1;
    caab -> 2;
    caabc -> 3;
    caabcd -> 4;
    cba -> 0;
    cbaa -> 1;
    cbaab -> 2;
    cbaabc -> 3;
    cbaabcd -> 4
  end.

test4(X) -> 
  case X of
    a -> 0;
    aa -> 1;
    aab -> 2;
    aabc -> 3;
    aabcd -> 4;
    ba -> 0;
    baa -> 1;
    baab -> 2;
    baabc -> 3;
    baabcd -> 4;
    ca -> 0;
    caa -> 1;
    caab -> 2;
    caabc -> 3;
    caabcd -> 4;
    cba -> 0;
    cbaa -> 1;
    cbaab -> 2;
    cbaabc -> 3;
    cbaabcd -> 4;
    aqqqqq -> 0;
    aaqqqqq -> 1;
    aabqqqqq -> 2;
    aabcqqqqq -> 3;
    aabcdqqqqq -> 4;
    baqqqqq -> 0;
    baaqqqqq -> 1;
    baabqqqqq -> 2;
    baabcqqqqq -> 3;
    baabcdqqqqq -> 4;
    caqqqqq -> 0;
    caaqqqqq -> 1;
    caabqqqqq -> 2;
    caabcqqqqq -> 3;
    caabcdqqqqq -> 4;
    cbaqqqqq -> 0;
    cbaaqqqqq -> 1;
    cbaabqqqqq -> 2;
    cbaabcqqqqq -> 3;
    cbaabcdqqqqq -> 4
  end.


my_reverse([], Acc) -> Acc;
my_reverse([X|Xs], Acc) ->
  my_reverse(Xs, [X|Acc]).

append([H|T], Z) ->
   append2(T, Z);
append([], X) ->
   X.

append2([H|T], Z) ->
   append(T, Z);
append2([], X) ->
   X.

 make_list(0, Acc) -> Acc;
 make_list(N, Acc) -> make_list(N-1,[N|Acc]).
