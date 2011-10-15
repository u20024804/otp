%% -*- erlang-indent-level: 2 -*-
%%
%% LLVM Backend Driver Module
%%
-module(hipe_llvm_main).
-export([rtl_to_native/3, remove_intermediate_file/1]).

-include("../main/hipe.hrl").
-include("../rtl/hipe_literals.hrl").

-define(NR_ARG_REGS, ?AMD64_NR_ARG_REGS).

rtl_to_native(RTL, Roots, Options) ->
  %% Get LLVM Instruction List
  {LLVMCode, RelocsDict, ConstMap, ConstAlign, ConstSize, SwitchList} =
  hipe_rtl2llvm:translate(RTL, Roots),
  %% Write LLVM Assembly to intermediate file
  Fun = hipe_rtl:rtl_fun(RTL),
  {Mod_Name, Fun_Name, Arity} = hipe_rtl2llvm:fix_mfa_name(Fun),
  Filename = atom_to_list(Fun_Name) ++ "_" ++ integer_to_list(Arity),
  %% Save temp files in /tmp. (XXX: Use a random folder)
  {ok, File_llvm} = file:open("/tmp/" ++ Filename ++ ".ll", [write]),
  hipe_llvm:pp_ins_list(File_llvm, LLVMCode),
  %% Invoke LLVM compiler tool to produce an object file
  ObjectFile = compile_with_llvm("/tmp/", Filename, Options),
  %% Remove .ll file
  spawn(?MODULE, remove_intermediate_file, ["/tmp/"++Filename++".ll"]),
  %% Extract information from object file
  ObjBin = elf64_format:open_object_file(ObjectFile),
  %% Get relocation info
  Relocs = elf64_format:get_text_symbol_list(ObjBin),
  %% Get stack descriptors
  SDescs = note_erlgc:get_sdesc_list(ObjBin),
  %% Get Labels info
  Labels = elf64_format:get_label_list(ObjBin),
  SwitchAddends = elf64_format:get_text_rodata_list(ObjBin),
  SwitchInfos = extract_switch_infos(SwitchAddends, Labels),
  %% Merge SwitchList labels with label offsets from object file, insert
  %% switch jump table constants to dictionary and update ConstMap with
  %% jump table.
  {FinalConstMap, FinalLabelMap, FinalConstSize, RelocsDict1} =
        fix_labelmap(SwitchList, SwitchInfos, ConstMap, ConstSize, RelocsDict),
  %% Create relocation list
  {Relocs1, Closures} = fix_relocations(Relocs, RelocsDict1, Mod_Name),
  SDescs2 = fix_sdescs(RelocsDict, Relocs1,  SDescs, Closures),
  FinalRelocs = [{4, SDescs2}|Relocs1],
  %% Get binary code and write to file
  BinCode = elf64_format:extract_text(ObjBin),
  %% Remove .o file
  spawn(?MODULE, remove_intermediate_file, ["/tmp/"++Filename++".opt.o"]),
  %%ok = file:write_file(Filename ++ "_code.o", BinCode, [binary]),
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
    FinalConstSize,
    FinalConstMap,
    %% XXX: Remove this reverse!!
    lists:reverse(FinalLabelMap),
    ExportMap,
    CodeSize,
    CodeBinary,
    Refs),
  Bin.

remove_intermediate_file(FileName) ->
  os:cmd("rm "++FileName).


%%----------------------------------------------------------------------------
%%------------------------- LLVM TOOL CHAIN ---------------------------------
%%----------------------------------------------------------------------------
%% Compile with LLVM tools
%%----------------------------------------------------------------------------
compile_with_llvm(Dir, Fun_Name, Options) ->
  %Opt_filename = opt(Fun_Name),
  %llc(Opt_filename, Fun_Name),  %XXX: Both names needed. FIX THIS SHIT
  %llvmc(Fun_Name).
  myllvmc(Dir, Fun_Name, Options).


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


%% My LLVMC that triggers everything (uses bitcode for intermediate files)
myllvmc(Dir, Fun_Name, Options) ->
  AsmFile  = Dir ++ Fun_Name ++ ".ll",
  %% Write object files to /tmp
  ObjectFile = "/tmp/" ++ Fun_Name ++ ".opt.o",
  OptFlags = ["-mem2reg", "-strip-debug"],
  LlcFlags = ["-O3", "-load=ErlangGC.so", "-code-model=medium",
      "-stack-alignment=8", "-tailcallopt"],
  SaveTemps =
    case proplists:get_bool(llvm_save_temps, Options) of
      true -> "--save-temps";
      false -> ""
    end,
  Command = "llvmc "++SaveTemps++" -opt -Wo" ++ fix_opts(OptFlags, ",") ++
     " -Wllc" ++ fix_opts(LlcFlags, ",") ++
     " -c " ++ AsmFile ++ " -o " ++ ObjectFile,
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, llvmc, Error})
  end,
  ObjectFile.


fix_opts(Opts) ->
  lists:foldl(fun(X, Acc) -> Acc ++ X end, "", Opts).

-define(Stringify(S), "\"" ++ S ++ "\"").
fix_opts(Opts, Sep) ->
  lists:foldl(fun(X, Acc) -> Acc ++ Sep ++ ?Stringify(X) end, "", Opts).


%%----------------------------------------------------------------------------
%% Functions to manage relocations
%%----------------------------------------------------------------------------

extract_switch_infos([], _L) -> [];
extract_switch_infos(Switches, Labels) ->
  %% Switches = [{SwitchName, ValueOffsets, Size}]
  %% io:format("Switches: ~w~n", [Switches]),
  %% Sort "Switches" based on "ValueOffsets"
  OffsetSortedSw = lists:ukeysort(2, Switches),
  %% Unzip offset-sorted list of "Switches"
  {Names, Offsets, SwitchSizeList} = lists:unzip3(OffsetSortedSw),
  %% Associate switch names with labels
  L = elf64_format:split_list(Labels, SwitchSizeList),
  %% Zip back! (to [{SwitchName, Offsets, Values}])
  lists:zip3(Names, Offsets, L).

%% This function handles the creation and declaration of jump tables
%% created for switch RTL statements. First switch jump tables are
%% inserted to relocation dictionary to refer to the jump table constant
%% in the code. Secondly the switch label list is merged with the label offsets
%% from the object file in order to create the LabelMap. Finally a jump table
%% for each entry in LabelMap is created and it is inserted to ConstMap.
fix_labelmap([], [], ConstMap, ConstSize, Relocs) ->
  {ConstMap, [], ConstSize, Relocs};
fix_labelmap(SwitchList, SwitchInfos, ConstMap, ConstSize, Relocs) ->
  MaxConst = case ConstMap of
    [] -> -1;
    _ -> find_max_constant(ConstMap, 0)
  end,
  Relocs1 = labels_to_dict(SwitchList, Relocs, MaxConst+1),
  Fun1 = fun(X) -> merge_labelmap(X, SwitchInfos) end,
  LabelMap = lists:map(Fun1, SwitchList),
  {JumpTables, NewLabelMap, NewConstSize} =
    create_jmp_constants(LabelMap, MaxConst+1, ConstSize),
  {ConstMap++JumpTables, NewLabelMap, NewConstSize, Relocs1}.


labels_to_dict([], Dict, _) ->  Dict;
labels_to_dict([{TableName, _}|Rest], Dict, RodataNumber) ->
  Dict1 = dict:store(TableName, {constant, RodataNumber}, Dict),
  labels_to_dict(Rest, Dict1, RodataNumber+1).

%% Merge Switch labels with label offsets from object file
merge_labelmap({Name, {switch, {_, _LabelList, NrLabels, []}}}, SwitchInfos) ->
  {Name, _, Labels} =  lists:keyfind(Name, 1, SwitchInfos),
  {unsorted, lists:zip(lists:seq(0, NrLabels*8-1,8), Labels)};
merge_labelmap({Name, {switch, {_, _LabelList, NrLabels, SortOrder}}}, SwitchInfos) ->
  {Name, _, Labels} =  lists:keyfind(Name, 1, SwitchInfos),
  {sorted, NrLabels, lists:zip(SortOrder, Labels)}.

%% For each entry in LabelMap, create the necessary constant that is a
%% a list of zeros with the correct size. For sorted labels, the offset in the
%% LabelMap must correspond to the offset in the ConstMap.
create_jmp_constants(LabelMap, MaxConst, ConstSize) ->
  create_jmp_constants(LabelMap, MaxConst, ConstSize, [], []).

create_jmp_constants([], _, ConstSize,  JmpAcc, LabelAcc) ->
  {un_tuplify_4(JmpAcc), lists:reverse(LabelAcc), ConstSize};
create_jmp_constants([Label|Ls], ConstNum, ConstSize,  JmpAcc, LabelAcc) ->
  ZeroBlock = create_zeros(Label),
  NewJmpTable = {ConstNum, ConstSize, 1, ZeroBlock},
  NewLabel = change_offset(Label, ConstSize),
  create_jmp_constants(Ls, ConstNum+1, ConstSize+length(ZeroBlock), [NewJmpTable|JmpAcc], [NewLabel|LabelAcc]).

%% Change offset in LabelMap
change_offset({sorted, _Offset, Sorted}, NewOffset) -> {sorted, NewOffset, Sorted};
change_offset(Label, _) -> Label.

%% Create a list of zeros of the correct size
create_zeros({sorted, Size, _Sorted}) ->
  lists:duplicate(Size*8, 0);
create_zeros({unsorted, Unsorted}) ->
  lists:duplicate(length(Unsorted)*8, 0).

%% Find the max constant that exists in a LabelMap
find_max_constant([], Max) -> Max;
find_max_constant([A,_B,_C,_D|Rest], Max) when A>Max -> find_max_constant(Rest,A);
find_max_constant([_A,_B,_C,_D|Rest], Max) -> find_max_constant(Rest,Max).

%% Untuplify a ConstMap. Returned in Reversed way!!!
un_tuplify_4(ConstMap) -> un_tuplify_4(ConstMap, []).

un_tuplify_4([], Acc) -> Acc;
un_tuplify_4([{A,B,C,D}|Rest], Acc) -> un_tuplify_4(Rest, [A,B,C,D|Acc]).

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
      NR = {BifName, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3], Acc4);
    {call, {hipe_bifs, llvm_expose_closure, A}} ->
      NR = {{hipe_bifs, llvm_expose_closure, 0}, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3], [{Offset,
        A}|Acc4]);
    %% MFA calls to functions in the same module are of type 3, while all
    %% other MFA calls are of type 2.
    {call, {ModName,_F,_A}=MFA} ->
      NR = {MFA, Offset},
      fix_relocs(Rs, RelocsDict, ModName, Acc0, Acc1, Acc2, [NR|Acc3], Acc4);
    {call, MFA} ->
      NR = {MFA, Offset},
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


%%----------------------------------------------------------------------------
%% Fixing Stack Descriptors
%%----------------------------------------------------------------------------

closures_offsets_arity([], SDescs) -> SDescs;
closures_offsets_arity(Closures, SDescs) ->
  {_,Offsets1} = lists:unzip(SDescs),
  Offsets2 = lists:sort(lists:flatten(Offsets1)),
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
