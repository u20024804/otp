%% -*- erlang-indent-level: 2 -*-
%%
%% LLVM Backend Driver Module
%%
-module(hipe_llvm_main).
-export([rtl_to_native/2]).

-include("../main/hipe.hrl").
-include("../rtl/hipe_literals.hrl").

-define(NR_ARG_REGS, ?AMD64_NR_ARG_REGS).

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
  SwitchAddends = elf64_format:get_text_rodata_list(ObjBin),
  %% Create final LabelMap
  LabelMap = fix_labelmap(Relocs, TempLabelMap, Labels, SwitchAddends),
  %% Create relocation list
  {Relocs1, Closures} = fix_relocations(Relocs, RelocsDict, Mod_Name),
  SDescs2 = fix_sdescs(RelocsDict, Relocs1,  SDescs, Closures),
  FinalRelocs = [{4, SDescs2}|Relocs1],
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
    lists:flatten(LabelMap),
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
  Options = ["-O3", "-code-model=medium", "-load=ErlangGC.so",
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
%%fix_labels(TempLabelMap, Labels) ->
%%  LabelsLength = length(Labels),
%%  sort_switches([], LabelsLength),
%%  Lengths = lists:map(fun export_length/1, TempLabelMap),
%%  Labels2 = elf64_format:split_list(Labels, Lengths),
%%  {_, Labels3} = lists:unzip(Labels2),
%%  Labels3.

%%export_length({_, L, []}) -> L;
%%export_length({_, sorted, L, _}) -> round(L/8).

fix_labelmap(Relocs, TempLabelMap, LabelList, SwitchAddends) ->
  Switches = merge_switches(Relocs, SwitchAddends),
  LabelList2 = split_labels(LabelList, Switches),
  A = lists:zip(TempLabelMap, LabelList2),
  lists:map(fun fix_labelmap2/1, A).

fix_labelmap2({M, Labels}) ->
  case M of
    {_, _, []} ->
      [{unsorted, lists:zip(lists:seq(0, length(Labels)*8-1,8), Labels)}];
    {_, sorted, Length, SortedBy} ->
      [{sorted, Length, lists:zip(SortedBy,Labels)}]
  end.

merge_switches(_Relocs, []) -> [];
merge_switches(_Relocs, {".rodata", []}) -> [];
merge_switches(Relocs, {".rodata", Addends}) ->
  case lists:keyfind(".rodata", 1, Relocs) of
    false ->
      [];
    {".rodata", Offsets} ->
      lists:zip(Offsets,Addends)
  end.

split_labels(LabelList, Switches) ->
  LabelsLength = length(LabelList),
  Switches1 = lists:keysort(2, Switches),
  Switches2 = find_switch_length(Switches1, LabelsLength),
  {Offsets, Lengths} = lists:unzip(Switches2),
  LabelList2 = elf64_format:split_list(LabelList, Lengths),
  Switches3 = lists:zip(Offsets, LabelList2),
  Switches4 = lists:keysort(1, Switches3),
  {_, LabelList3} =  lists:unzip(Switches4),
  LabelList3.


find_switch_length(Switches, LabelsLength) ->
  Switches1 = lists:map(fun ({X,Y}) -> {X, Y div 8} end, Switches),
  find_switch_length(Switches1, LabelsLength, []).
find_switch_length([], _LabelsLength, Acc) ->
  Acc;
find_switch_length([{Offset, Addend}], LabelsLength, Acc) ->
  lists:reverse([{Offset, LabelsLength-Addend}|Acc]);
find_switch_length([{Offset1, Addend1}, {Offset2, Addend2}|Rest], LL, Acc) ->
  find_switch_length([{Offset2, Addend2}|Rest], LL, [{Offset1,
        Addend2-Addend1}|Acc]).

%% Correlate object file relocation symbols with info from translation to llvm
%% code. Also split relocations according to their type, as expected by the
%% hipe_unified_loader.
fix_relocations(Relocs, RelocsDict, ModName) ->
  Relocs1 = fix_rodata(Relocs),
  fix_relocs(Relocs1, RelocsDict, ModName, [], [], [], [], []).

fix_relocs([], _, _, Acc0, Acc1, Acc2, Acc3, Acc4) ->
  Relocs = [{0, Acc0}, {1, Acc1}, {2, Acc2}, {3, Acc3}],
  %% Remove Empty Elements
  NotEmpty =
    fun ({_, X}) ->
        case X of [] -> false;
          _ -> true
        end
    end,
    {lists:filter(NotEmpty, Relocs), Acc4};

fix_relocs([{Name, Offset}|Rs], RelocsDict, ModName, Acc0, Acc1, Acc2, Acc3,
  Acc4) ->
  case dict:fetch(Name, RelocsDict) of
    {atom, AtomName} ->
      NR = {AtomName, Offset},
      fix_relocs(Rs, RelocsDict, ModName, [NR|Acc0], Acc1, Acc2, Acc3, Acc4);
    {constant, _}=Constant ->
      NR = {Constant, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, [NR|Acc1], Acc2, Acc3, Acc4);
    {closure, _}=Closure ->
      NR = {Closure, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, [NR|Acc1], Acc2, Acc3, Acc4);
    {call, {bif, BifName, _}} ->
      NR = {fix_reloc_name(BifName), Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3], Acc4);
    {call, {hipe_bifs, llvm_expose_closure, A}} ->
      NR = {{hipe_bifs, llvm_expose_closure, 0}, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3], [{Offset,
        A}|Acc4]);
    %% MFA calls to functions in the same module are of type 3, while all
    %% other MFA calls are of type 2.
    {call, {ModName,F,A}} ->
      NR = {{ModName,fix_reloc_name(F),A}, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3], Acc4);
    {call, {M,F,A}} ->
      NR = {{M,fix_reloc_name(F),A}, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, [NR|Acc2], Acc3, Acc4);
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
      fix_rodata(Rs, Num+1, fix_rodata_1(Offset)++Acc);
    _ ->
      fix_rodata(Rs, Num, [R|Acc])
  end.

fix_rodata_1(Offset) -> fix_rodata_1(Offset, 0, []).

fix_rodata_1([], _, Acc) -> Acc;
fix_rodata_1([O|Os], Base, Acc) ->
  NewName = ".rodata"++integer_to_list(Base),
  fix_rodata_1(Os, Base+1, [{NewName, [O]}|Acc]).

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
%% Fixing Stack Descriptors
%%----------------------------------------------------------------------------
closures_offsets_arity([], SDescs) -> SDescs;
closures_offsets_arity(Closures, SDescs) ->
  {_,Offsets1} = lists:unzip(SDescs),
  Offsets2 = lists:flatten(Offsets1),
  Foo =
  fun ({Off, Arity}) ->
      [I|_] = lists:dropwhile(fun (Y) -> Y<Off+5 end, Offsets2),
      {I, Arity}
  end,
  Foo2 = fun ({OffList, Arity}) -> lists:map(fun(X) -> Foo({X,Arity}) end,
        OffList) end,
  lists:map(Foo2, Closures).


%% This function is responssible for correcting the stack descriptors of the
%% calls that are found in the code and have more than NR_ARG_REGS(so
%% some of their arguments are passed to the stack). Because of the
%% Reserved Call Frame that the LLVM uses, the stack descriptors are no the
%% correct since at the point of call the frame size is reduced proportionally
%% to the number of arguments that are passed to the stack. Also the offsets
%% of the roots need to be readjusted.
fix_sdescs(RelocsDict, Relocs, SDescs, Closures) ->
  NeedsSDescFix  = calls_with_stack_args(RelocsDict),
  OffsetsArity = calls_offsets_arity(Relocs, NeedsSDescFix),
  OffsetsArity2 = lists:flatten(closures_offsets_arity(Closures,SDescs)),
  %io:format("Closures before ~w~n", [Closures]),
  %io:format("Closures ~w~n", [OffsetsArity2]),
  hipe_llvm_bin:merge_refs(fix_sdescs1(SDescs, OffsetsArity++OffsetsArity2)).
  %lists:map(fun live_args/1, Foo).


%% This function takes as argument the relocation dictionary as produced by the
%% translation of RTL code to LLVM and finds the names of the calls (MFA and
%% BIF calls) that have more than NR_ARG_REGS.
calls_with_stack_args(Dict) ->
  HasStackArgs =
    fun(_, Value) ->
        case Value of
          {call, {_,_,Arity}} when Arity>?NR_ARG_REGS ->
            true;
          _ ->
            false
        end
    end,
  Calls1 = dict:filter(HasStackArgs, Dict),
  Calls2 = dict:to_list(Calls1),
  FindNameArity =
    fun({_, {call, Y}}) ->
        case Y of
          {bif, Name, Arity} ->
            {Name, Arity};
          MFA ->
            MFA
        end
    end,
  lists:map(FindNameArity, Calls2).

%% This functions extracts the stack arity and the offset in the code of the
%% calls that have stack arguments.
calls_offsets_arity(Relocs, CallsWithStackArgs) ->
  {_, Calls1} = lists:unzip(lists:filter(
    fun ({X,_}) ->
        case X of 3 -> true;
          2-> true;
          _ -> false
        end
    end, Relocs)),
  Calls2 = lists:flatten(Calls1),
  OffsetsArity1 = lists:map(
    fun(X) -> case lists:keyfind(X, 1, Calls2) of
          {X, Offs} ->
            Arity = case X of
              {_, A} -> A;
              {_, _, A} -> A
            end,
            lists:map(fun(Z) -> {Z+4, Arity-?NR_ARG_REGS} end, Offs);
          false -> []
        end
    end, CallsWithStackArgs),
  lists:flatten(OffsetsArity1).

fix_sdescs1(SDescs, OffsetsArity) ->
  lists:foldl(fun fix_sdescs2/2, SDescs, OffsetsArity).

fix_sdescs2(OffsetsArity, SDescs) ->
  lists:foldl(
    fun(X, Acc) -> fix_sdescs3(OffsetsArity, X) ++ Acc end, [], SDescs).

%% If the offset of the call belongs to the offsets of the sdesc then
%% remove the offset from the sdesc and create a new desc with the correct
%% frame size and roots offsets.
fix_sdescs3({Offset, Arity}, {{ ExnHandler, FrameSize, StkArity, Roots},
            OldOffsets} = SDesc) ->
  DecRoot = fun(X) -> X-Arity end,
  case lists:member(Offset, OldOffsets) of
    false ->
      [SDesc];
    true ->
      NewRootsList = lists:map(DecRoot, tuple_to_list(Roots)),
      NewSDesc =
      case length(NewRootsList)>0 andalso (hd(NewRootsList)>=0) of
        true ->
          {{ExnHandler, FrameSize-Arity, StkArity, list_to_tuple(NewRootsList)},
            [Offset]};
        false ->
          {{ExnHandler, FrameSize, StkArity, Roots}, [Offset]}
      end,
      RestOffsets = lists:delete(Offset, OldOffsets),
      RestSDesc = {{ExnHandler, FrameSize, StkArity, Roots},
        RestOffsets},
      [NewSDesc,  RestSDesc]
  end.

%%----------------------------------------------------------------------------

%%live_args({{ExnHandler, FrameSize, Arity, RootSet},Offs}=A) ->
%%  case Arity>0 of
%%    false ->A;
%%    true ->
%%      ArgRoots = lists:seq(1,Arity),
%%      ArgRoots2 = lists:map(fun(X) -> X+FrameSize end, ArgRoots),
%%      Mpla1 = tuple_to_list(RootSet),
%%      NewRootSet = lists:append(Mpla1, ArgRoots2),
%%      Mpla2= list_to_tuple(NewRootSet),
%%      {{ExnHandler, FrameSize, Arity, Mpla2}, Offs}
%%  end.
