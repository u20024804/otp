-module(hipe_llvm_bin).

-export([join_binaries/3]).

-export([
  mk_llvm_bin/10,
  llvm_bin_version/1,
  llvm_bin_checksum/1,
  llvm_bin_constalign/1,
  llvm_bin_constsize/1,
  llvm_bin_constmap/1,
  llvm_bin_labelmap/1,
  llvm_bin_exportmap/1,
  llvm_bin_codesize/1,
  llvm_bin_codebinary/1,
  llvm_bin_refs/1
]).

%%----------------------------------------------------------------------------
%% Abstraction For LLVM Object File
%%----------------------------------------------------------------------------
-record(llvm_bin, 
      {version, checksum, constalign, constsize, constmap, 
        labelmap, exportmap, codesize, codebinary, refs}).

mk_llvm_bin(Version, Checksum, Constalign, Constsize, Constmap, 
  Labelmap, Exportmap, Codesize, Codebinary, Refs) -> 
              #llvm_bin{version=Version, checksum=Checksum, 
                            constalign=Constalign, constsize=Constsize, 
                            constmap=Constmap, labelmap=Labelmap,
                            exportmap=Exportmap, codesize=Codesize,
                            codebinary=Codebinary, refs=Refs}.

llvm_bin_version(#llvm_bin{version=Version}) -> 
  Version.
llvm_bin_checksum(#llvm_bin{checksum=Checksum}) -> 
  Checksum.
llvm_bin_constalign(#llvm_bin{constalign=Constalign}) -> 
  Constalign.
llvm_bin_constsize(#llvm_bin{constsize=Constsize}) -> 
  Constsize.
llvm_bin_constmap(#llvm_bin{constmap=Constmap}) -> 
  Constmap.
llvm_bin_labelmap(#llvm_bin{labelmap=Labelmap}) ->
  Labelmap.
llvm_bin_exportmap(#llvm_bin{exportmap=Exportmap}) -> 
  Exportmap.
llvm_bin_codesize(#llvm_bin{codesize=Codesize}) -> 
  Codesize.
llvm_bin_codebinary(#llvm_bin{codebinary=Codebinary}) ->
  Codebinary.
llvm_bin_refs(#llvm_bin{refs=Refs}) -> Refs.

%%----------------------------------------------------------------------------


%%----------------------------------------------------------------------------
%% Join llvm_binaries as produced by whole module compilation.
%% We join the binary code and compute total code size.
%% Also update offsets to exportmap, labelmap and refs.
%% Finally we assign unique labels to constants and 
%% update Constmap and Refs.
%%----------------------------------------------------------------------------
join_binaries(Binaries, Closures, Exports) ->
  Version = llvm_bin_version(lists:nth(1,Binaries)),
  CheckSum = llvm_bin_checksum(lists:nth(1,Binaries)),
  {CodeSize, CodeBinary, ExportMap} = join_code(Binaries),
  %io:format("CodeSize
  %  ~w~nCodeBinary~w~nExportMap~w~n",[CodeSize,CodeBinary,ExportMap]),
  LabelMap = correct_label_offsets(Binaries, ExportMap),
 % io:format("LabelMap ~w~n",[LabelMap]),
  {ConstAlign, ConstSize} = correct_align_size(Binaries),
  {ConstMap, Refs} = join_relocations(Binaries, ExportMap),
%  io:format("ConstMap ~w ~nRefs ~wn",[ConstMap, Refs]),
  FinalExportMap =  fix_exportmap(ExportMap, Closures, Exports),
  ConstMap1 = filter_empty_list(ConstMap),
  LabelMap1= filter_empty_list(LabelMap),
  {FinalConstMap, FinalLabelMap} = compute_const_size(ConstMap1, LabelMap1),
  term_to_binary([{Version, CheckSum},
   ConstAlign, ConstSize, FinalConstMap, FinalLabelMap, FinalExportMap,
   CodeSize,  CodeBinary,  Refs,
   0,[] % ColdSize, CRrefs
 ]).

%%----------------------------------------------------------------------------


%%----------------------------------------------------------------------------
%% Misc Functions
%%----------------------------------------------------------------------------

%% Join binary code and compute code size.
%% Also fix exportmap with correct code offset
join_code(Binaries) -> join_code(Binaries, 0, <<>>, []).

join_code([], CodeSize, CodeBinary, ExportMap) -> 
  {CodeSize, CodeBinary, lists:reverse(ExportMap)};

join_code([#llvm_bin{codesize=CodeSize, codebinary=CodeBinary,
      exportmap=ExportMap} | Rest], SizeAcc, BinaryAcc, ExportAcc) ->
  {M,F,A} = ExportMap,
  NewExportMap = {SizeAcc, M, F, A},
  join_code(Rest, SizeAcc+CodeSize, <<BinaryAcc/binary, CodeBinary/binary>>,
            [NewExportMap|ExportAcc]).

%%----------------------------------------------------------------------------

%% Add correct offset to each label in LabelMap
correct_label_offsets(Binaries, ExportMap) -> 
  correct_label_offsets(Binaries, ExportMap, []).

correct_label_offsets([], [], LabelAcc) ->
  lists:reverse(lists:flatten(LabelAcc));
correct_label_offsets([#llvm_bin{labelmap=LabelMap}|Rest],
                    [E|Es], LabelAcc) ->
  {Offset, _, _, _} = E,
  NewLabelMap = add_offset_to_labels(LabelMap, Offset),
  correct_label_offsets(Rest, Es, [NewLabelMap|LabelAcc]).

add_offset_to_labels(LabelMap, Offset) ->
  AddOffset =
    fun (X) ->
        case X of
          {unsorted, UnSorted} -> {unsorted, lists:map(fun ({A,B}) -> {A,B+Offset} end, UnSorted)};
          {sorted, Num, Sorted} -> 
            {sorted, Num, lists:map(fun ({A,B}) -> {A,B+Offset} end, Sorted)}
        end
    end,
  lists:map(AddOffset, LabelMap).
  
%%----------------------------------------------------------------------------

%% Find ConstAlign and ConstSize. They are the max of the ConstAlign
%% and the sum of ConstSize of each MFA.
correct_align_size(Binaries) ->
  MaxAlign = fun (#llvm_bin{constalign=Align}, Acc) -> max(Align, Acc) end,
  ConstAlign = lists:foldl(MaxAlign, 0, Binaries),
  AddSize = fun (#llvm_bin{constsize=Size}, Acc) -> Acc+Size end,
  ConstSize = lists:foldl(AddSize, 0, Binaries),
  {ConstAlign, ConstSize}.


%%----------------------------------------------------------------------------

%% Remove Empty Lists from a list
filter_empty_list(List) -> filter_empty_list(List, []).

filter_empty_list([], Acc) -> lists:reverse(Acc);
filter_empty_list([E|Es], Acc) -> 
  case E of 
    [] -> filter_empty_list(Es, Acc);
    Other -> filter_empty_list(Es, [Other|Acc])
  end.

%% Give unique labels to constants, and update them in Refs.
%% Also add correct offset to each relocation in Refs.
join_relocations(Binaries, ExportMap) ->
  join_relocations(Binaries, ExportMap, [] ,[], 10000).

join_relocations([], [], ConstAcc, RefAcc, _) ->
  ConstAcc1= tuplify_4(ConstAcc),
  ConstAcc2 = lists:reverse(ConstAcc1),
  ConstAcc3= un_tuplify_4(ConstAcc2),
  {ConstAcc3, RefAcc};


join_relocations([Bin|Bs], [Export|Es], ConstAcc, RefAcc, BaseLabel) ->
  {Offset, _, _, _} = Export,
  ConstMap = llvm_bin_constmap(Bin),
  Refs = llvm_bin_refs(Bin),
  {NewConstMap, Refs2, NewBaseLabel} = unique_const_labels(ConstMap, Refs,
    BaseLabel),
  NewRefs = add_offset_to_relocs(Refs2, Offset),
  join_relocations(Bs, Es, NewConstMap++ConstAcc, NewRefs++RefAcc,
    NewBaseLabel).

unique_const_labels(ConstMap, Refs, BaseLabel) ->
  ConstMap1 = tuplify_4(ConstMap),
  ConstLength = length(ConstMap1),
  ConstMap2 = lists:map(fun({Label,A,B,Const}) -> {Label+BaseLabel,A,B,Const}
    end, ConstMap1),
  ConstMap3 = un_tuplify_4(lists:reverse(ConstMap2)),
  NewRefs = substitute_const_label(Refs, BaseLabel),
  {ConstMap3, NewRefs, BaseLabel+ConstLength}.

%% Convert constmap in tuples of 4 elements
tuplify_4(ConstMap) -> tuplify_4(ConstMap, []).
tuplify_4([], Acc) -> Acc;
tuplify_4([A,B,C,D|Rest], Acc) -> tuplify_4(Rest, [{A,B,C,D}|Acc]).

un_tuplify_4(ConstMap) -> un_tuplify_4(ConstMap, []).
un_tuplify_4([], Acc) -> Acc;
un_tuplify_4([{A,B,C,D}|Rest], Acc) -> un_tuplify_4(Rest, [A,B,C,D|Acc]).

substitute_const_label(Refs, Base) ->
  Check_Const =
    fun ({X, List}) ->
        case X of
          {constant, Label} -> {{constant, Base+Label}, List};
          _ -> {X,List}
        end
    end,
  Check_Type = 
    fun ({X, List}) ->
        case X of 
            1 -> {X, lists:map(Check_Const, List)};
            _ -> {X, List}
          end
    end,
  lists:map(Check_Type, Refs).

add_offset_to_relocs(Refs, Size) ->
  Update_reloc = fun (X) -> X+Size end,
  Update_exn_label = fun (X) -> 
      case X of
        {[], _, _, _} = A -> A;
        {ExnLabel,FrameSize,Arity,BitMap} -> {ExnLabel+Size, FrameSize, Arity,
            BitMap};
        Other -> Other
      end
  end,
  Update_relocs = fun({X, Relocs}) -> {Update_exn_label(X), lists:map(Update_reloc, Relocs)} end,
  Update_all = fun ({Type, Relocs}) -> {Type, lists:map(Update_relocs, Relocs)} end,
  lists:map(Update_all, Refs).


%%----------------------------------------------------------------------------

%% Update ExportMap with information about whether a function is a closure
%% and whether it is exported.
fix_exportmap([{Addr,M,F,A}|Rest], Closures, Exports) ->
  IsClosure = lists:member({M,F,A}, Closures),
  IsExported = is_exported(F, A, Exports),
  [Addr,M,F,A,IsClosure,IsExported | fix_exportmap(Rest, Closures, Exports)];
fix_exportmap([],_,_) -> [].
is_exported(F, A, Exports) -> lists:member({F,A}, Exports).

%%----------------------------------------------------------------------------

%% Fix Constant offsets in Constmap. Also update corresponding
%% offsets in LabelMap
compute_const_size(ConstMap, LabelMap) ->
  ConstMap1 = tuplify_4(ConstMap),
  {ConstMap2, LabelMap2} = compute_const_size(lists:reverse(ConstMap1), LabelMap, 0, [], []),
  %io:format("--> ConstMap2 ~w~n", [ConstMap2]),
  %ConstMap4= lists:reverse(ConstMap3),
  ConstMap3 = un_tuplify_4(ConstMap2),
  {ConstMap3, LabelMap2}.

compute_const_size([], [], _, ConstAcc, LabelAcc) -> 
  {ConstAcc, lists:reverse(LabelAcc)};
compute_const_size([{Label, Offset, Type, Constant}|Rest], LabelMap,
  Base, ConstAcc, LabelAcc) ->
  case Type of
    0 -> compute_const_size(Rest, LabelMap, Base, [{Label, Offset, Type,
            Constant}|ConstAcc], LabelAcc);
    1 -> 
      %% In this case there should be an entry in LabelMap for this constant
      %% block
      case LabelMap of
        [] -> 
          compute_const_size(Rest, LabelMap, Base+length(Constant), [{Label, Base, Type,
                Constant}|ConstAcc], LabelAcc);
        Other -> 
          [L|Ls] =LabelMap,
          %% Check whether the sizes of the constant and the label match
          case check_sizes(Constant, L) of
            match -> 
              NewLabel = fix_label_offset(L, Base),
              compute_const_size(Rest, Ls, Base+length(Constant), [{Label, Base, Type,
                    Constant}|ConstAcc], NewLabel++LabelAcc);
            no_match ->
              compute_const_size(Rest, LabelMap, Base+length(Constant), [{Label, Base, Type,
                    Constant}|ConstAcc], LabelAcc)
          end
    end;
  2 -> compute_const_size(Rest, LabelMap, Base+8*length(Constant), [{Label, Base, Type,
          Constant}|ConstAcc], LabelAcc)
end.

fix_label_offset({sorted, _, Sorted}, Offset) -> [{sorted,Offset,Sorted}];
fix_label_offset( {unsorted, Unsorted}, Offset) -> lists:map(fun({A,B}) ->
        {A+Offset,B} end, Unsorted).

check_sizes(Constant, Label) ->
  LabelSize = 
  case Label of
    {sorted,_, Sorted} -> length(Sorted)*8;
    {unsorted,Unsorted} -> length(Unsorted)*8
  end,
  case length(Constant) of
    LabelSize -> 
      match;
    Other ->
      io:format("No Constant/Label match:~nconst_size~w~nlabel_size:~w~n", [length(Constant),LabelSize]),
      no_match
  end.
