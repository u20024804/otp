-module(hipe_llvm_merge).

-export([finalize/3]).

-include("hipe_llvm_arch.hrl").
-include("../../kernel/src/hipe_ext_format.hrl").
-include("../rtl/hipe_literals.hrl").
-include("../main/hipe.hrl").

finalize(CompiledCode, Closures, Exports) ->
  CompiledCode1 = [ CodePack || {_, CodePack} <- CompiledCode],
  Code = [ {MFA, [], ConstTab} ||
           {MFA, _, _ , ConstTab, _, _} <- CompiledCode1],
  {ConstAlign, ConstSize, ConstMap, RefsFromConsts} =
    hipe_pack_constants:pack_constants(Code, ?ARCH_REGISTERS:alignment()),
  {CodeSize, CodeBinary, ExportMap} = merge_code(CompiledCode1),
  AccRefs = merge_refs(CompiledCode1, ConstMap),
  %% Bring CompiledCode to a combine_label_maps-acceptable form.
  CompiledCode2 = [ {MFA, Code, CodeSize, LabelMap} ||
                    {MFA, Code, CodeSize, _, _, LabelMap} <- CompiledCode1 ],
  LabelMap = hipe_pack_constants:combine_label_maps(CompiledCode2, 0,
                                                    gb_trees:empty()),
  SC = hipe_pack_constants:slim_constmap(ConstMap),
  DataRelocs = hipe_pack_constants:mk_data_relocs(RefsFromConsts, LabelMap),
  SSE = hipe_pack_constants:slim_sorted_exportmap(ExportMap, Closures, Exports),
  SlimRefs = hipe_pack_constants:slim_refs(AccRefs),
  term_to_binary([{?VERSION_STRING(),?HIPE_SYSTEM_CRC},
      ConstAlign, ConstSize,
      SC,  % ConstMap
      DataRelocs, % LabelMap
      SSE, % ExportMap
      CodeSize, CodeBinary, SlimRefs,
      0,[] % ColdCodeSize, SlimColdRefs
  ]).

%% @doc Merge the MFAs' binary code to one continuous binary and compute the
%%      size of this binary. In the same time create an exportmap in a form
%%      of {Address, M, F, A}.
merge_code(CompiledCode) ->
  merge_code(CompiledCode, 0, <<>>, []).

%% XXX: What about alignment?
merge_code([], CodeSize, CodeBinary, ExportMap) ->
  {CodeSize, CodeBinary, ExportMap};
merge_code([{{M, F, A}, CodeBinary, CodeSize, _, _, _}|Rest],
  TotalSize, TotalBinary, ExportMap) ->
  merge_code(Rest, TotalSize+CodeSize, <<TotalBinary/binary, CodeBinary/binary>>,
             [{TotalSize, M, F, A}|ExportMap]).

%% @doc Merge the references to relocatable symbols in the binary code. The
%%      offsets must be updated because of the merging of the code binaries!
merge_refs(CompiledCode, ConstMap) ->
  merge_refs(CompiledCode, ConstMap, 0, []).

merge_refs([], _, _, Acc) -> Acc;
merge_refs([{MFA, _, CodeSize, _, Refs, _}|Rest], ConstMap, TotalSize, Acc) ->
  %% Important!: The hipe_pack_constants:pack_constants/2 function assignes
  %% unique numbers to constants (ConstNo). This numbers are used from now on,
  %% instead of labels that were used before. So, in order to be compatible, we
  %% must change all the constant labels in the Refs to the corresponding
  %% ConstNo, that can be found in the ConstMap (#pcm_entry{}).
  UpdatedRefs = labels_to_numbers(MFA, Refs, ConstMap),
  NewRefs = lists:map(fun(X) -> add_offset_to_ref(X, TotalSize) end,
                      UpdatedRefs),
  merge_refs(Rest, ConstMap, TotalSize+CodeSize, NewRefs++Acc).

labels_to_numbers(MFA, Refs, ConstMap) ->
  UpdateRef =
    fun (X) ->
      case X of
        {Type, Offset, {constant, Label}} ->
          ConstNo = hipe_pack_constants:find_const({MFA, Label}, ConstMap),
          {Type, Offset, {constant, ConstNo}};
        Other ->
          Other
      end
    end,
  lists:map(UpdateRef, Refs).

%% @doc Update offset to a reference. In case of stack descriptors we must check
%%      if there exists an exception handler, because it must also be updated.
add_offset_to_ref({?SDESC, Offset, SDesc}, CodeAddr) ->
  case SDesc of
    {[], _, _, _} -> %% No handler. Only update offset
      {?SDESC, Offset+CodeAddr, SDesc};
    {ExnHandler, FrameSize, StackArity, Roots} -> %% Also update exception handler
      {?SDESC, Offset+CodeAddr, {ExnHandler+CodeAddr, FrameSize, StackArity, Roots}}
  end;
add_offset_to_ref({Type, Offset, Term}, CodeAddr) ->
  {Type, Offset+CodeAddr, Term}.
