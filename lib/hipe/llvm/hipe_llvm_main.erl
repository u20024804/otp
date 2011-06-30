%% -*- erlang-indent-level: 2 -*-
%%
%% LLVM Backend Driver Module
%%
-module(hipe_llvm_main).
-export([rtl_to_native/2]).

-include("../main/hipe.hrl").
-include("../rtl/hipe_literals.hrl").

patch_labels([],[])->[];
patch_labels([M|_], Labels) ->
  case M of
    {_, []} ->
      [{unsorted, lists:zip(lists:seq(0, length(Labels)*8-1,8), Labels)}];
    {_, sorted, Length, SortedBy} ->
      [{sorted, Length, lists:zip(SortedBy,Labels)}]
  end.

rtl_to_native(RTL, _Options) ->
  %% Get LLVM Instruction List
  {LLVMCode, RefDict, ConstMap, ConstAlign, ConstSize, TempLabelMap} = hipe_rtl2llvm:translate(RTL),
  %% Write LLVM Assembly to intermediate file
  Fun = hipe_rtl:rtl_fun(RTL),
  IsClosure = hipe_rtl:rtl_is_closure(RTL),
  {Mod_Name, FN, Arity} =  Fun,
  Fun_Name =
  case IsClosure of
    false ->
      FN;
    true ->
      hipe_rtl2llvm:fix_closure_name(FN)
  end,
  Filename = atom_to_list(Fun_Name) ++ "_" ++ integer_to_list(Arity),
  {ok, File_llvm} = file:open(Filename ++ ".ll", [write]),
  hipe_llvm:pp_ins_list(File_llvm, LLVMCode),
  %% Invoke LLVM compiler tool to produce an object file
  Object_filename = compile_with_llvm(Filename),
  %% Extract information from object file
  ObjBin = elf64_format:open_object_file(Object_filename),
  %% Get relocation info and write to file for loader
  Relocs = elf64_format:get_call_list(ObjBin),
  %% Get stack descriptors
  SDescs = note_erlgc:get_sdesc_list(ObjBin), 
  %% Get Labels info
  Labels = elf64_format:get_label_list(ObjBin),
  LabelMap = patch_labels(TempLabelMap, Labels),
  %% Temporary code for creating references needed by  the loader
  Relocs1 = lists:map(fun({A,B}) -> {map_funs(A, RefDict), B} end, Relocs),
  Is_mfa = 
    fun ({Function,_}) ->
      case Function of
        {Mod_Name, _, _} -> false;
        {_, _, _} -> true;
        _ -> false
      end 
    end,
  Is_constant = 
    fun ({A, _}) ->
      case A of
        {constant, _} -> true;
        _ -> false
      end
    end,
  Is_closure =
    fun ({A,_}) ->
        case A of
          {closure, _} -> true;
          _ -> false
        end
    end,
  Is_atom = 
    fun ({A, _}) ->
      case A of
        {'atom', _} -> true;
        _ -> false
      end
    end,
  {MFAs, Rest} = lists:partition(Is_mfa, Relocs1),
  {Constants, Rest1} = lists:partition(Is_constant, Rest),
  {Closures, Rest2} = lists:partition(Is_closure, Rest1),
  {Atoms1, BIFs} = lists:partition(Is_atom, Rest2),
  Atoms = lists:map(fun ({{'atom', Name}, X}) -> {Name,X} end, Atoms1),
  FinalRelocs = [{2, MFAs},{3, BIFs}, {1, Constants},{1,Closures}, {0, Atoms},
                  {4, SDescs}],
  ok = file:write_file(Filename ++ "_relocs.o", erlang:term_to_binary(FinalRelocs), [binary]),
  %% Get binary code and write to file for loader
  BinCode = elf64_format:extract_text(ObjBin),
  ok = file:write_file(Filename ++ "_code.o", BinCode, [binary]),
  %%--------------------------------------------------------------------------
  %% Create All Information needed by the hipe_unified_loader
  %% No Labelmap Used yet..
  %% As Fun Name we must pass the original name
  ExportMap = {Mod_Name, FN, Arity},
  CodeSize = byte_size(BinCode),
  CodeBinary = BinCode,
  Refs = lists:filter(
    fun ({_, X}) -> 
        case X of [] -> false;
          _ -> true 
        end 
    end,
    FinalRelocs), 
  Bin = hipe_llvm_bin:mk_llvm_bin(
    ?VERSION_STRING(),
    ?HIPE_SYSTEM_CRC,
    ConstAlign,
    ConstSize,
    ConstMap,
    LabelMap,
    ExportMap,
    CodeSize,
    CodeBinary,
    Refs),
  Bin.


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
  Options = ["-O3", "-code-model=medium", "-load=libErlangGC.so"],
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
  FName = case Name of
    ".rodata" -> ".rodata0";
    _ -> Name
  end,
  case dict:fetch("@"++FName, Dict) of
    {'constant', Label} -> {'constant', Label};
    {'atom', AtomName} -> {'atom', AtomName};
    {closure, Closure} -> {closure, Closure};
    {BifName} -> map_bifs(BifName);
    {M,F,A} -> {M,map_bifs(F),A};
    Other -> exit({?MODULE,map_funs,{"Unknown call", Other}})
  end.

%% Ugly..Just for testing reasons
map_bifs(Name) ->
  case Name of
    bif_add -> '+';
    bif_sub -> '-';
    bif_mul -> '*';
    bif_div -> 'div';
    concat -> '++';
    unary_plus -> '+';
    Other -> Other
  end.

