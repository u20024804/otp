%% -*- erlang-indent-level: 2 -*-
%%
%% LLVM Backend Driver Module
%%
-module(hipe_llvm_main).
-export([rtl_to_native/2]).


rtl_to_native(RTL, Options) ->
  %% Get LLVM Instruction List
  {LLVMCode, RefDict} = hipe_rtl2llvm:translate(RTL),
  %% Write LLVM Assembly to intermediate file
  Fun = hipe_rtl:rtl_fun(RTL),
  {Mod_Name, Fun_Name, _} = Fun,
  {ok, File_llvm} = file:open(atom_to_list(Fun_Name) ++ ".ll", [write]),
  hipe_llvm:pp_ins_list(File_llvm, LLVMCode),
  %% Invoke LLVM compiler tool to produce an object file
  {ok, Object_File} = llvmc(atom_to_list(Fun_Name)),
  %% Extract information from object file
  ObjBin = elf64_format:open_object_file(Object_File),
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


llvmc(Fun_Name) -> 
  Options = ["-O3", "-code-model=medium"],
  llvmc(Fun_Name, Options).

llvmc(Fun_Name, Options) ->
  Llvm_File = Fun_Name++".ll",
  Object_File = Fun_Name++".o",
  Options2 = lists:foldl(fun(X, Acc) -> Acc++" "++X end, "", Options),
  Command = "llvmc "++Options2++" -o "++Object_File++" -c "++Llvm_File,
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, llvmc, Error})
  end,
  {ok, Object_File}.


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
