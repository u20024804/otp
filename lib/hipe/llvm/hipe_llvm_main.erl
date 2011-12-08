%% -*- erlang-indent-level: 2 -*-
-module(hipe_llvm_main).

-export([rtl_to_native/4,
         remove_folder/1]).

-include("../main/hipe.hrl").
-include("../rtl/hipe_literals.hrl").
-include("../../kernel/src/hipe_ext_format.hrl").
-include("hipe_llvm_arch.hrl").

%% @doc Translation of RTL to a loadable object. This functions takes the RTL
%% code and calls hipe_rtl2llvm:translate/2 to translate the RTL code to LLVM
%% code. After this, LLVM asm is printed to a file and the LLVM tool chain is
%% invoked in order to produce an object file. Then the elf64_format and the
%% note_erlc modules are used in order to extract all the necessary informations
%% on the object file.
rtl_to_native(MFA, RTL, Roots, Options) ->
  %% Compile to LLVM and get Instruction List (along with infos)
  {LLVMCode, RelocsDict, ConstTab} =
    hipe_rtl2llvm:translate(RTL, Roots),
  %% Fix Fun_Name to an acceptable LLVM identifier (needed for closures)
  {_Mod_Name, Fun_Name, Arity} = hipe_rtl2llvm:fix_mfa_name(MFA),
  %% Write LLVM Assembly to intermediate file (on disk)
  {ok, Dir, ObjectFile} = compile_with_llvm(Fun_Name, Arity, LLVMCode, Options, false),
  %%
  %% Extract information from object file
  %%
  ObjBin = elf64_format:open_object_file(ObjectFile),
  %% Get relocation info
  Relocs = elf64_format:get_text_symbol_list(ObjBin),
  %% Get stack descriptors
  SDescs = note_erlgc:get_sdesc_list(ObjBin),
  %% Get labels info
  Labels = elf64_format:get_label_list(ObjBin),
  SwitchAddends = elf64_format:get_text_rodata_list(ObjBin),
  SwitchInfos = extract_switch_infos(SwitchAddends, Labels),
  %% Labelmap contains the offsets of the labels in the code that are
  %% used for switch's jump tables
  LabelMap = create_labelmap(MFA, SwitchInfos, RelocsDict),
  %% AccRefs contains the offsets of all references to relocatable symbols in
  %% the code
  %% Closures containts offsets and arity of calls to hipe_bifs:llvm_expose_closure/A.
  {AccRefs, ExposedClosures} = fix_relocations(Relocs, RelocsDict, MFA),
  %% FixedSDescs are the stack descriptors after correcting calls that have
  %% arguments in the stack
  FixedSDescs = fix_stack_descriptors(RelocsDict, AccRefs, SDescs, ExposedClosures),
  Refs = AccRefs++FixedSDescs,
  %% Get binary code from object file
  BinCode = elf64_format:extract_text(ObjBin),
  %% Remove temp files (if needed)
	remove_temp_folder(Dir, Options),
  %% Return the code together with information that will be used in the
  %% hipe_llvm_merge module to produce the final binary that will be loaded
  %% by the hipe unified loader.
  {MFA, BinCode, byte_size(BinCode), ConstTab, Refs, LabelMap}.



%%------------------------------------------------------------------------------
%% LLVM tool chain
%%------------------------------------------------------------------------------

%% @doc Compile function Fun_Name/Arity to LLVM. Return Dir (in order to remove
%% it if we do not want to store temporary files) and ObjectFile name that is
%% created by the LLVM tools.
compile_with_llvm(Fun_Name, Arity, LLVMCode, Options, Buffer) ->
  Filename = atom_to_list(Fun_Name) ++ "_" ++ integer_to_list(Arity),
  %% Save temp files in a unique folder
  DirName = "llvm_" ++ unique_id() ++ "/",
  Dir =
    case proplists:get_bool(llvm_save_temps, Options) of
      true ->  %% Store folder in current directory
	  DirName;
      false -> %% Temporarily store folder in "/tmp" (rm afterwards)
	"/tmp/" ++ DirName
    end,
	%% Create temp directory
  os:cmd("mkdir " ++ Dir),
  %% Print LLVM assembly to file
  OpenOpts = [append, raw] ++
    case Buffer of
      true -> [delayed_write]; % Use delayed_write!
      false -> []
    end,
  {ok, File_llvm} = file:open(Dir ++ Filename ++ ".ll", OpenOpts),
  hipe_llvm:pp_ins_list(File_llvm, LLVMCode),
  %% delayed write can cause file:close not to do a close
  file:close(File_llvm),
  file:close(File_llvm),
  %% Invoke LLVM compiler tools to produce an object file
  ObjectFile = invoke_llvm_tools(Dir, Filename, Options),
  {ok, Dir, ObjectFile}.

%% @doc Invoke LLVM tools to compile function Fun_Name/Arity and create an
%% Object File.
invoke_llvm_tools(Dir, Fun_Name, Options) ->
  llvm_as(Dir, Fun_Name),
  llvm_opt(Dir, Fun_Name, Options),
  llvm_llc(Dir, Fun_Name, Options),
  compile(Dir, Fun_Name, "gcc").

%% @doc Invoke llvm-as tool to convert LLVM Asesmbly to bitcode.
llvm_as(Dir, Fun_Name) ->
  Source  = Dir ++ Fun_Name ++ ".ll",
  Dest    = Dir ++ Fun_Name ++ ".bc",
  Command = "llvm-as " ++ Source ++ " -o " ++ Dest,
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, opt, Error})
  end.

%% @doc Invoke opt tool to optimize the bitcode.
llvm_opt(Dir, Fun_Name, Options) ->
  Source   = Dir ++ Fun_Name ++ ".bc",
  Dest     = Source,
  OptLevel = trans_optlev_flag(opt, Options),
  OptFlags = [OptLevel, "-mem2reg", "-strip-debug"],
  Command  = "opt " ++ fix_opts(OptFlags) ++ " " ++ Source ++ " -o " ++ Dest,
  %% io:format("OPT: ~s~n", [Command]),
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, opt, Error})
  end.

%% @doc Invoke llc tool to compile the bitcode to native assembly.
llvm_llc(Dir, Fun_Name, Options) ->
  Source   = Dir ++ Fun_Name ++ ".bc",
  OptLevel = trans_optlev_flag(llc, Options),
  Align    = integer_to_list(?WORD_WIDTH div 8),
  LlcFlags = [OptLevel, "-load=ErlangGC.so", "-code-model=medium",
	      "-stack-alignment=" ++ Align, "-tailcallopt"],
  Command  = "llc " ++ fix_opts(LlcFlags) ++ " " ++ Source,
  %% io:format("LLC: ~s~n", [Command]),
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, opt, Error})
  end.

%% @doc Invoke the compiler tool ("gcc", "llvmc", etc.) to generate an object
%%      file from native assembly.
compile(Dir, Fun_Name, Compiler) ->
  Source  = Dir ++ Fun_Name ++ ".s",
  Dest    = Dir ++ Fun_Name ++ ".o",
  Command = Compiler ++ " -c " ++ Source ++ " -o " ++ Dest,
  case os:cmd(Command) of
    [] -> ok;
    Error -> exit({?MODULE, llvmc, Error})
  end,
  Dest.


%% Join options
fix_opts(Opts) ->
  string:join(Opts, " ").

%% Translate optimization-level flag (default is "none")
trans_optlev_flag(Tool, Options) ->
  Flag =
    case Tool of
      opt -> llvm_opt;
      llc -> llvm_llc
    end,
  case proplists:get_value(Flag, Options) of
    o0 -> ""; % "-O0" does not exist in opt tool
    o1 -> "-O1";
    o2 -> "-O2";
    o3 -> "-O3";
    undefined -> ""
  end.

%%------------------------------------------------------------------------------
%% Functions to manage relocations
%%------------------------------------------------------------------------------

%% @doc This function assocciates a jump table with the offset in the code
%% where it is appeared and mainly with the offets of the Labels which contains.
extract_switch_infos([], _L) -> [];
extract_switch_infos(Switches, Labels) ->
  %% Sort "Switches" based on "ValueOffsets"
  OffsetSortedSw = lists:ukeysort(2, Switches),
  %% Unzip offset-sorted list of "Switches"
  {Names, _Offsets, SwitchSizeList} = lists:unzip3(OffsetSortedSw),
  %% Associate switch names with labels
  L = elf64_format:split_list(Labels, SwitchSizeList),
  %% Zip back! (to [{SwitchName, Values}])
  lists:zip(Names, L).

%% @doc Create a gb_tree which contains information about the labels that used
%% for switch's jump tables. The keys of the gb_tree are of the form {MFA,
%% Label} and the Values are the actual Offsets
create_labelmap(MFA, SwitchInfos, RelocsDict) ->
  create_labelmap(MFA, SwitchInfos, RelocsDict, gb_trees:empty()).

create_labelmap(_, [], _, LabelMap) -> LabelMap;
create_labelmap(MFA, [{Name, Offsets} | Rest], RelocsDict, LabelMap) ->
  case dict:fetch(Name, RelocsDict) of
    {switch, {_TableType, LabelList, _NrLabels, _SortOrder}, _JTabLab} ->
      KVDict = lists:ukeysort(1, lists:zip(LabelList, Offsets)),
      NewLabelMap = insert_to_labelmap(KVDict, LabelMap),
      create_labelmap(MFA, Rest, RelocsDict, NewLabelMap);
    _ ->
      exit({?MODULE, create_labelmap, "Not a jump table!~n"})
  end.

%% Insert a list of [{Key,Value}] to a LabelMap (gb_tree)
insert_to_labelmap([], LabelMap) -> LabelMap;
insert_to_labelmap([{Key, Value}|Rest], LabelMap) ->
  case gb_trees:lookup(Key, LabelMap) of
    none ->
      insert_to_labelmap(Rest, gb_trees:insert(Key, Value, LabelMap));
    {value, Value} -> %% Exists with the *exact* same Value.
      insert_to_labelmap(Rest, LabelMap)
  end.

%% @doc Correlate object file relocation symbols with info from translation to
%% llvm code.
fix_relocations(Relocs, RelocsDict, MFA ) ->
  fix_relocs(Relocs, RelocsDict, MFA, [], []).

%% ClosureAcc holds the offsets and the arity of calls to
%% hipe_bifs:llvm_expose_closure/A which is used to expose the closures
%% addresses.
fix_relocs([], _, _, RelocAcc, ClosureAcc) -> {RelocAcc, ClosureAcc};
fix_relocs([{Name, Offset}|Rs], RelocsDict, {ModName,_,_}=MFA,  RelocAcc,
           ClosureAcc) ->
  case dict:fetch(Name, RelocsDict) of
    {atom, AtomName} ->
      fix_relocs(Rs, RelocsDict, MFA, [{?LOAD_ATOM, Offset, AtomName}|RelocAcc],
                 ClosureAcc);
    {constant, Label} ->
      fix_relocs(Rs, RelocsDict, MFA, [{?LOAD_ADDRESS, Offset,
                 {constant, Label}}|RelocAcc], ClosureAcc);
    {switch, _, JTabLab} -> %% Treat switch exactly as constant
      fix_relocs(Rs, RelocsDict, MFA, [{?LOAD_ADDRESS, Offset,
                 {constant, JTabLab}}|RelocAcc], ClosureAcc);
    {closure, _}=Closure ->
      fix_relocs(Rs, RelocsDict, MFA,
                 [{?LOAD_ADDRESS, Offset, Closure}|RelocAcc], ClosureAcc);
    {call, {bif, BifName, _}} ->
      fix_relocs(Rs, RelocsDict,
                 MFA, [{?CALL_LOCAL, Offset, BifName}|RelocAcc], ClosureAcc);
    {call, {hipe_bifs, llvm_expose_closure, A}} ->
      %% Map llvm_expose_closure/a to llvm_expose_closure/0, The argument arity
      %% is used only as a trick in order to extract the stack arity of the
      %% following closure.
      CallMFA = {hipe_bifs, llvm_expose_closure, 0},
      fix_relocs(Rs, RelocsDict, MFA, [{?CALL_LOCAL, Offset, CallMFA}|RelocAcc],
                 [{Offset, A} | ClosureAcc]);
    %% MFA calls to functions in the same module are of type 3, while all
    %% other MFA calls are of type 2.
    {call, {ModName,_F,_A}=CallMFA} ->
      fix_relocs(Rs, RelocsDict, MFA, [{?CALL_LOCAL, Offset, CallMFA}|RelocAcc],
                 ClosureAcc);
    {call, CallMFA} ->
      fix_relocs(Rs, RelocsDict, MFA,
                 [{?CALL_REMOTE, Offset, CallMFA}|RelocAcc], ClosureAcc);
    Other ->
      exit({?MODULE, fix_relocs, {"Relocation Not In Relocation Dictionary",
		  Other}})
  end.

%%------------------------------------------------------------------------------
%% Fixing Stack Descriptors
%%------------------------------------------------------------------------------

%% @doc This function is responssible for correcting the stack descriptors of
%% the calls that are found in the code and have more than NR_ARG_REGS(so some
%% of their arguments are passed to the stack). Because of the Reserved Call
%% Frame that the LLVM uses, the stack descriptors are no the correct since at
%% the point of call the frame size is reduced proportionally to the number of
%% arguments that are passed to the stack. Also the offsets of the roots need
%% to be readjusted.
fix_stack_descriptors(RelocsDict, Relocs, SDescs, ExposedClosures) ->
  %% NamedCalls are MFA and BIF calls that need fix
  NamedCalls  = calls_with_stack_args(RelocsDict),
  NamedCallsOffs = calls_offsets_arity(Relocs, NamedCalls),
  ClosuresOffs = closures_offsets_arity(ExposedClosures, SDescs),
  fix_sdescs(NamedCallsOffs++ClosuresOffs, SDescs).

%% @doc This function takes as argument the relocation dictionary as produced
%% by the translation of RTL code to LLVM and finds the names of the calls (MFA
%% and BIF calls) that have more than NR_ARG_REGS.
calls_with_stack_args(Dict) ->
  calls_with_stack_args(dict:to_list(Dict), []).

calls_with_stack_args([], Calls) -> Calls;
calls_with_stack_args([ {_Name, {call, {M, F, A}}} | Rest], Calls)
                      when A > ?NR_ARG_REGS ->
  Call =
    case M of
      bif -> {F,A};
      _ -> {M,F,A}
    end,
  calls_with_stack_args(Rest, [Call|Calls]);
calls_with_stack_args([_|Rest], Calls) ->
  calls_with_stack_args(Rest, Calls).

%% @doc This functions extracts the stack arity and the offset in the code of
%% the named calls (MFAs, BIFs) that have stack arguments.
calls_offsets_arity(AccRefs, CallsWithStackArgs) ->
  calls_offsets_arity(AccRefs, CallsWithStackArgs, []).

calls_offsets_arity([], _, Acc) -> Acc;
calls_offsets_arity([{Type, Offset, Term} | Rest], CallsWithStackArgs, Acc)
                    when Type == ?CALL_REMOTE orelse Type == ?CALL_LOCAL ->
  case lists:member(Term, CallsWithStackArgs) of
    true ->
      Arity =
        case Term of
          {_M, _F, A} -> A;
          {_F, A} -> A
        end,
      calls_offsets_arity(Rest, CallsWithStackArgs,
                          [{Offset + 4, Arity - ?NR_ARG_REGS}|Acc]);
    false ->
      calls_offsets_arity(Rest, CallsWithStackArgs, Acc)
  end;
calls_offsets_arity([_|Rest], CallsWithStackArgs, Acc) ->
  calls_offsets_arity(Rest, CallsWithStackArgs, Acc).

%% @doc this functions extract that stack arity and the offsets in the code of
%% closures that have stack arity. The Closures argument represent the
%% hipe_bifs:llvm_exposure_closure/0 calls in the code. The actual closure is
%% the next call in the code, so the offset of the next call must be found from
%% the stack descriptors.
closures_offsets_arity([], _) ->
  [];
closures_offsets_arity(ExposedClosures, SDescs) ->
  Offsets = [ Offset || {_, Offset, _} <- SDescs ],
  SortedOffsets = lists:sort(Offsets), %% Offsets must be sorted in order
                                       %% FindTheClosure fun to work
  FindTheClosure =
    fun ({Off, Arity}) ->
      [I|_] = lists:dropwhile(fun (Y) -> Y<Off+5 end, SortedOffsets),
      {I, Arity}
    end,
  lists:map(FindTheClosure, ExposedClosures).

%%%% The below functions correct the arity of calls, that are identified by
%%%% offset, in the stack descriptors.
fix_sdescs([], SDescs) -> SDescs;
fix_sdescs([{Offset, Arity} | Rest], SDescs) ->
  case lists:keyfind(Offset, 2, SDescs) of
    false ->
      fix_sdescs(Rest, SDescs);
    {?SDESC, Offset, SDesc}->
      {ExnHandler, FrameSize, StkArity, Roots} = SDesc,
      DecRoot = fun(X) -> X-Arity end,
      NewRootsList = lists:map(DecRoot, tuple_to_list(Roots)),
      NewSDesc =
        case length(NewRootsList) > 0 andalso hd(NewRootsList) >= 0 of
          true ->
            {?SDESC, Offset, {ExnHandler, FrameSize-Arity, StkArity,
              list_to_tuple(NewRootsList)}};
          false ->
            {?SDESC, Offset, {ExnHandler, FrameSize, StkArity, Roots}}
        end,
      RestSDescs = lists:keydelete(Offset, 2, SDescs),
      fix_sdescs(Rest, [NewSDesc | RestSDescs])
  end.


%%------------------------------------------------------------------------------
%% Miscellaneous functions
%%------------------------------------------------------------------------------

remove_temp_folder(Dir, Options) ->
  case proplists:get_bool(llvm_save_temps, Options) of
    true -> ok;
    false -> spawn(?MODULE, remove_folder, [Dir])
  end.

remove_folder(FolderName) ->
  os:cmd("rm -r " ++ FolderName).

unique_id() ->
  integer_to_list(erlang:phash2({node(),now()})).
