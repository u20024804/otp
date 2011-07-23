%% -*- erlang-indent-level: 2 -*-
%%
%% LLVM Backend Driver Module
%%
-module(hipe_llvm_main).
-export([rtl_to_native/2]).

-include("../main/hipe.hrl").
-include("../rtl/hipe_literals.hrl").

rtl_to_native(RTL, _Options) ->
  %% Get LLVM Instruction List
  {LLVMCode, RelocsDict, ConstMap, ConstAlign, ConstSize, TempLabelMap} = hipe_rtl2llvm:translate(RTL),
  %% Write LLVM Assembly to intermediate file
  Fun = hipe_rtl:rtl_fun(RTL),
  {Mod_Name, Fun_Name, Arity} = hipe_rtl2llvm:fix_mfa_name(Fun),
  Filename = atom_to_list(Fun_Name) ++ "_" ++ integer_to_list(Arity),
  {ok, File_llvm} = file:open(Filename ++ ".ll", [write]),
  hipe_llvm:pp_ins_list(File_llvm, LLVMCode),
  %% Invoke LLVM compiler tool to produce an object file
  Object_filename = compile_with_llvm(Filename),
  %% Extract information from object file
  ObjBin = elf64_format:open_object_file(Object_filename),
  %% Get relocation info
  Relocs = elf64_format:get_text_symbol_list(ObjBin),
  %% Get stack descriptors
  SDescs = note_erlgc:get_sdesc_list(ObjBin), 
  %% Get Labels info
  Labels = elf64_format:get_label_list(ObjBin),
  %% Create final LabelMap
  LabelMap = fix_labelmap(TempLabelMap, Labels),
  %% Create relocation list
  Relocs1 = fix_relocations(Relocs, RelocsDict, Mod_Name),
  FinalRelocs = [{4, SDescs}|Relocs1],
  %% Get binary code and write to file
  BinCode = elf64_format:extract_text(ObjBin),
  ok = file:write_file(Filename ++ "_code.o", BinCode, [binary]),
  %%--------------------------------------------------------------------------
  %% Create All Information needed by the hipe_unified_loader
  %% No Labelmap Used yet..
  %% As Fun Name we must pass the original name
  ExportMap = Fun,
  CodeSize = byte_size(BinCode),
  CodeBinary = BinCode,
  Refs = FinalRelocs,
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

%%----------------------------------------------------------------------------
%%------------------------- LLVM TOOL CHAIN ---------------------------------
%%----------------------------------------------------------------------------
%% Compile with LLVM tools
%%----------------------------------------------------------------------------
compile_with_llvm(Fun_Name) ->
  Opt_filename = opt(Fun_Name),
  llc(Opt_filename, Fun_Name),  %XXX: Both names needed. FIX THIS SHIT
  llvmc(Fun_Name).


%% OPT wrapper (.ll -> .ll)
opt(Fun_Name) ->
  Options = ["-mem2reg", "-O2"], %XXX: Do we want -O3?
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
  Options = ["-O3", "-code-model=medium", "-load=libErlangGC.so",
	     "-stack-alignment=8", "-tailcallopt"],
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

fix_opts(Opts) ->
  lists:foldl(fun(X, Acc) -> Acc++" "++X end, "", Opts).

%%----------------------------------------------------------------------------

%%----------------------------------------------------------------------------
%% Functions to manage relocations
%%----------------------------------------------------------------------------

fix_labelmap([],[])->[];
fix_labelmap([M|_], Labels) ->
  case M of
    {_, []} ->
      [{unsorted, lists:zip(lists:seq(0, length(Labels)*8-1,8), Labels)}];
    {_, sorted, Length, SortedBy} ->
      [{sorted, Length, lists:zip(SortedBy,Labels)}]
  end.

%% Correlate object file relocation symbols with info from translation to llvm
%% code. Also split relocations according to their type, as expected by the
%% hipe_unified_loader.
fix_relocations(Relocs, RelocsDict, ModName) ->
  Relocs1 = fix_rodata(Relocs),
  fix_relocs(Relocs1, RelocsDict, ModName, [], [], [], []).

fix_relocs([], _, _, Acc0, Acc1, Acc2, Acc3) ->
  Relocs = [{0, Acc0}, {1, Acc1}, {2, Acc2}, {3, Acc3}],
  %% Remove Empty Elements
  NotEmpty = 
    fun ({_, X}) -> 
        case X of [] -> false;
          _ -> true 
        end 
    end,
  lists:filter(NotEmpty, Relocs);

fix_relocs([{Name, Offset}|Rs], RelocsDict, ModName, Acc0, Acc1, Acc2, Acc3) ->
  case dict:fetch(Name, RelocsDict) of
    {atom, AtomName} ->
      NR = {AtomName, Offset},
      fix_relocs(Rs, RelocsDict, ModName, [NR|Acc0], Acc1, Acc2, Acc3);
    {constant, _}=Constant ->
      NR = {Constant, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, [NR|Acc1], Acc2, Acc3);
    {closure, _}=Closure ->
      NR = {Closure, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, [NR|Acc1], Acc2, Acc3);
    {call, {bif, BifName, _}} ->
      NR = {fix_reloc_name(BifName), Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3]);
    %% MFA calls to functions in the same module are of type 3, while all
    %% other MFA calls are of type 2.
    {call, {ModName,F,A}} ->
      NR = {{ModName,fix_reloc_name(F),A}, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3]);
    {call, {M,F,A}} ->
      NR = {{M,fix_reloc_name(F),A}, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, [NR|Acc2], Acc3);
    Other ->
      exit({?MODULE, fix_relocs, {"Relocation Not In Relocation Dictionary", Other}})
  end.

%% Temporary function that gives correct names to symbols that correspond to
%% .rodata section, which are produced from switch statement translation.
fix_rodata(Relocs) ->
  fix_rodata(Relocs, 0, []).
fix_rodata([], _, Acc) -> Acc;
fix_rodata([{Name, Offset}=R|Rs], Num, Acc) ->
  case Name of
    ".rodata" -> 
      NewName = ".rodata"++integer_to_list(Num),
      fix_rodata(Rs, Num+1, [{NewName, Offset}|Acc]);
    _ -> 
      fix_rodata(Rs, Num, [R|Acc])
  end.

fix_reloc_name(Name) ->
  case Name of
    bif_add -> '+';
    bif_sub -> '-';
    bif_mul -> '*';
    bif_div -> 'div';
    concat -> '++';
    unary_plus -> '+';
    Other -> Other
  end.

%%----------------------------------------------------------------------------
