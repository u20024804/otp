%% -*- erlang-indent-level: 2 -*-
%%
%% LLVM Backend Driver Module
%%
-module(hipe_llvm_main).
-export([rtl_to_native/2]).


rtl_to_native(RTL, _Options) ->
  %% Get LLVM Instruction List
  {LLVMCode, RefDict} = hipe_rtl2llvm:translate(RTL),
  %% Write LLVM Assembly to intermediate file
  Fun = hipe_rtl:rtl_fun(RTL),
  {Mod_Name, Fun_Name, _} = Fun,
  {ok, File_llvm} = file:open(atom_to_list(Fun_Name) ++ ".ll", [write]),
  hipe_llvm:pp_ins_list(File_llvm, LLVMCode),
  %% Invoke LLVM compiler tool to produce an object file
  Filename = atom_to_list(Fun_Name),
  Object_filename = compile_with_llvm(Filename),
  %% Extract information from object file
  ObjBin = elf64_format:open_object_file(Object_filename),
  %% Get relocation info and write to file for loader
  Relocs = elf64_format:get_call_list(ObjBin),
  Relocs1 = lists:map(fun({A,B}) -> {map_funs(A, RefDict), B} end, Relocs),
  Is_mfa = 
    fun ({Function,_}) ->
      case Function of
        {Mod_Name, _, _} -> false;
        {_, _, _} -> true;
        _ -> false
      end 
    end,
  {MFAs, BIFs} = lists:partition(Is_mfa, Relocs1),
  FinalRelocs = [{2, MFAs},{3, BIFs}],
  ok = file:write_file("relocs.o", erlang:term_to_binary(FinalRelocs), [binary]),
  %% Get binary code and write to file for loader
  BinCode = elf64_format:extract_text(ObjBin),
  ok = file:write_file("code.o", BinCode, [binary]),
  {BinCode, FinalRelocs}.


fix_opts(Opts) ->
  lists:foldl(fun(X, Acc) -> Acc++" "++X end, "", Opts).


%% Compile with LLVM tools
compile_with_llvm(Fun_Name) ->
  Opt_filename = opt(Fun_Name),
  llc(Opt_filename, Fun_Name),  %XXX: Both names needed. FIX THIS SHIT
  llvmc(Fun_Name).

  
%% OPT wrapper (.ll -> .ll)
opt(Fun_Name) ->
  Options = ["-O3"],
  opt(Fun_Name, Options).

opt(Fun_Name, Opts) ->
  Llvm_file = Fun_Name ++ ".ll",
  Opt_llvm_filename = Fun_Name ++ "_42_", %New (optimized) file
  Opt_llvm_file = Opt_llvm_filename ++ ".ll",
  Command = "opt " ++ fix_opts(Opts) ++ " -S" ++ " -o " ++ Opt_llvm_file ++ " "
    ++ Llvm_file,
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, opt, Error})
  end,
  Opt_llvm_filename.


%% LLC wrapper (.ll -> .s)
llc(Opt_filename, Fun_Name) ->
  Options = ["-O3", "-code-model=medium"],
  llc(Opt_filename, Fun_Name, Options).

llc(Opt_filename, Fun_Name, Opts) ->
  Llvm_file = Opt_filename ++ ".ll",
  Asm_file = Fun_Name ++ ".s",
  Command = "llc " ++ fix_opts(Opts) ++ " " ++ Llvm_file ++ " -o " ++ Asm_file,
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, llvmc, Error})
  end.


%% LLVMC wrapper (.s -> .o)
llvmc(Fun_Name) -> 
  Options = [],
  llvmc(Fun_Name, Options).

llvmc(Fun_Name, Opts) ->
  Asm_File = Fun_Name++".s",
  Object_filename = Fun_Name ++ ".o",
  Command = "llvmc " ++ fix_opts(Opts) ++ " -c " ++ Asm_File ++ " -o " ++
    Object_filename,
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, llvmc, Error})
  end,
  Object_filename.


map_funs(Name, Dict) ->
    B = 
    case dict:fetch("@"++Name, Dict) of
      {BifName} -> map_bifs(BifName);
      {M,F,A} -> {M,F,A};
      _ -> exit({?MODULE,map_funs,"Unknown call"})
    end,
    io:format("~nFOOO ~w~n", [B]), B.

%% Ugly..Just for testing reasons
map_bifs(Name) ->
  case Name of
    bif_add -> '+';
    bif_sub -> '-';
    bif_mul -> '*';
    bif_div -> 'div';
    Other -> Other
  end.
