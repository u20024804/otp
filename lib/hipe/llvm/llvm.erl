%%
%% Temporary Module for incorporating LLVM
%%
-module(llvm).
-export([compile/1,assemble/1,extract_bin/1,run_all/1]).


compile(Name) ->
  os:cmd("llc -O3 -o temp.s "++Name++".ll"),
  os:cmd("awk '{if ($1==\".Leh_func_end0:\") {exit} else {print $0}}' temp.s > "++Name++".s").

compile_with_opt(Name) ->
  os:cmd("opt -O3 -S -o foo.ll"++Name++".ll"),
  os:cmd("mv foo.ll "++Name++".ll").


assemble(Name) ->
  os:cmd("as -o "++Name++".o "++Name++".s").

extract_bin(Name) ->
  os:cmd("cp "++Name++".o foo.o"),
  os:cmd("cp "++Name++".o temp.o"),
  os:cmd("objcopy -O binary foo.o"),
  os:cmd("ndisasm -b 64 foo.o").
  
run_all(Name) ->
  compile(Name),
  assemble(Name),
  extract_bin(Name).
