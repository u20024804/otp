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
