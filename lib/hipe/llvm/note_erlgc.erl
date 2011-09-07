%% -*- erlang-indent-level: 2 -*-
%%% Copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%%                     Chris Stavrakakis <hydralisk.r@gmail.com>
%%%
%%% This file is part of elf64_format.
%%%
%%% elf64_format is free software: you can redistribute it and/or modify
%%% it under the terms of the GNU General Public License as published by
%%% the Free Software Foundation, either version 3 of the License, or
%%% (at your option) any later version.
%%%
%%% elf64_format is distributed in the hope that it will be useful,
%%% but WITHOUT ANY WARRANTY; without even the implied warranty of
%%% MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the
%%% GNU General Public License for more details.
%%%
%%% You should have received a copy of the GNU General Public License
%%% along with elf64_format. If not, see <http://www.gnu.org/licenses/>.

%%% @copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%%                      Chris Stavrakakis <hydralisk.r@gmail.com>
%%% @version {@version}
%%% @author Yiannis Tsiouris <yiannis.tsiouris@gmail.com>

%%% @doc This module contains functions that can be used to extract information
%%%      of a custom Note Section from an ELF-64 Object file. This section
%%%      (".note.gc") is emitted by ErlangGC LLVM plugin and is used in HiPE's
%%%      LLVM backend of Erlang/OTP sytem. The section contains in fact a Stack
%%%      descriptor for every safe point in the code segment.
%%%
%%%      The structure of the section is the following:
%%%
%%%       .long <n>       # number of safe points in code
%%% 
%%%       .long .L<label> # safe point address               |
%%%       .long <n>       # stack frame size (in words)      |-> fixed-size part
%%%       .long <n>       # stack arity                      |   of a safe point
%%%       .long <n>       # number of live roots that follow |
%%%
%%%       .long <n>       # live root's stack index  |
%%%          .....                                   |-> variable-sized part
%%%       .long <n>       #          >>              |   of a safe point
%%%       .long <n>       #          >>              |
-module(note_erlgc).

-export([
	 %% Safe point
	 get_safepoint_entries/1,
	 get_next_safepoint_entry/1,
	 %% Fixed-size part (header)
	 get_fixedsize_part/1,
	 get_fixedsize_part_field/2,
	 %% Variable-size part (live roots)
	 get_liveroots_part/1,
	 get_liveroots/2,
	 %% Stack descriptor
	 get_sdesc_list/1
	]).

-include("note_erlgc.hrl").


%%-------------------------------------------------------------------------------
%% Safe point manipulation
%%-------------------------------------------------------------------------------

%% @spec get_safepoint_count( binary() ) -> integer()
%% @doc Function that takes as argument a Note Section binary and returns the 
%%      number of safe points in it.
-spec get_safepoint_count( binary() ) -> integer().
get_safepoint_count(Note) ->
  elf64_format:get_field(Note, {integer, ?SP_COUNT}).


%% @spec get_safepoint_entries( binary() ) -> {integer(), binary()}
%% @doc Function that takes as argument a Note Section binary and returns a 
%%      tuple of `{SPCount, SPEntries}' with the number of safe point entries
%%      that section contained and the safe point entries binary (basically by
%%      removing the first word of the section that contains the number of safe
%%      point entries to follow).
-spec get_safepoint_entries( binary() ) -> {integer(), binary()}.
get_safepoint_entries(Note) ->
  SPCount = get_safepoint_count(Note),
  SPEntriesSize = byte_size(Note) - ?SP_COUNT_SIZE,
  SPEntries = elf64_format:get_binary_segment(Note, 
					      {0 + ?SP_COUNT_SIZE, SPEntriesSize}),
  {SPCount, SPEntries}.


%% @spec get_next_safepoint_entry( binary() ) -> binary()
%% @doc Extracts the first safe point entry of an Safe Point Entries binary. 
%%      Returns binary.
-spec get_next_safepoint_entry( binary() ) -> binary().
get_next_safepoint_entry(SPEntries) ->
  %% Get fixed-size part in order to find live root count 
  FixedSize = get_fixedsize_part(SPEntries),
  %% Get live root count
  LiveRootCnt = get_fixedsize_part_field(FixedSize, ?SP_LIVEROOTCNT),
  %% Return the whole sdesc
  VarSize = LiveRootCnt * ?LR_STKINDEX_SIZE,
  elf64_format:get_binary_segment(SPEntries, {0, ?SP_FIXED_SIZE + VarSize}).


%%-------------------------------------------------------------------------------
%% Manipulation of fixed-size part (header of a safe point entry)
%%-------------------------------------------------------------------------------

%% @spec get_fixedsize_part( binary() ) -> binary()
%% @doc Function that takes a Safe Point Entry as an argument and returns the 
%%      fixed-size part of the entry.
-spec get_fixedsize_part( binary() ) -> binary().
get_fixedsize_part(SPEntry) ->
  elf64_format:get_field(SPEntry, {binary, ?SP_FIXED}).


%% @spec get_fixedsize_part_field(binary(), {integer(), integer()}) -> integer()
%% @doc Extracts a specific field of a fixed size part of a safe point entry.
%%      This function should be used with the appropriate macros defined in 
%%      note_erlgc.hrl in order to be safe!
-spec get_fixedsize_part_field( binary(), {integer(), integer()} ) -> integer().
get_fixedsize_part_field(FixedSize, {Offset, Size}) ->
  elf64_format:get_field(FixedSize, {integer, {Offset, Size}}).


%%-------------------------------------------------------------------------------
%% Manipulation of variable-size part (liveroots)
%%-------------------------------------------------------------------------------

%% @spec get_liveroots_part( binary() ) -> binary()
%% @doc Extract the variable-size part (containing all live roots information) 
%%      of a Safe Point Entry. Returns binary.
-spec get_liveroots_part( binary() ) -> binary().
get_liveroots_part(SPEntry) ->
  VarSize = byte_size(SPEntry) - ?SP_FIXED_SIZE,
  elf64_format:get_binary_segment(SPEntry, {?SP_FIXED_SIZE, VarSize}).


%% @spec get_liveroots( binary(), integer() ) -> {integer()}
%% @doc Function that takes as argument a variable-size part of a safe point 
%%      (`LiveRootsEntry') and the number of roots in the entry (`NumOfRoots')
%%      and returns a tuple with the stack frame indexes of all the roots.
-spec get_liveroots( binary(), integer() ) -> {integer()}.
get_liveroots(LiveRootsEntry, NumOfRoots) ->
  IndexList = get_liveroots(LiveRootsEntry, NumOfRoots, []),
  erlang:list_to_tuple(IndexList).

-spec get_liveroots( binary(), integer(), [integer()] ) -> [ integer() ].
get_liveroots(_LiveRootsEntry, 0, Acc) ->
  Acc;
get_liveroots(LiveRootsEntry, NumOfRoots, Acc) ->
  Bits = ?bits(?LR_STKINDEX_SIZE),
  <<LRIndex:Bits/integer-little, LiveRootsEntry2/binary>> = LiveRootsEntry,
  get_liveroots(LiveRootsEntry2, NumOfRoots - 1, [LRIndex | Acc]).


%%-------------------------------------------------------------------------------
%% Manipulation of variable-size part (liveroots)
%%-------------------------------------------------------------------------------

%% @spec get_safepoint_addresses( binary(), integer() ) -> [integer()]
%% @doc Function that takes an appropriate Rela section, i.e. ".rela.gc", and 
%%      extracts information about all relocations of the custom Note Section 
%%      (".note.gc"). The relocations are actually the safe point labels and thus
%%      the safe point addresses. The relocations are (<b>assumed</b> to be)
%%      sorted by the order of appearance in the code segment. Returns a list
%%      with all the safe point addresses.
-spec get_safepoint_addresses( binary(), integer() ) -> [integer()].
get_safepoint_addresses(RelaGC, NumOfEntries) ->
  get_safepoint_addresses(RelaGC, NumOfEntries, []).

-spec get_safepoint_addresses( binary(), integer(), [integer()] ) -> [integer()].
get_safepoint_addresses(_RelaGC, 0, Acc) ->
  lists:reverse(Acc);
get_safepoint_addresses(RelaGC, NumOfEntries, Acc) ->
  %% Get first Rela entry
  RelaEntry = elf64_format:get_rela_entry(RelaGC, ?ELF64_RELA_SIZE, 0),
  %% Get Rela entry's offset
  RelaOff = elf64_format:get_rela_entry_field(RelaEntry, ?R_ADDEND),
  %% Continue with more Rela entries
  <<_Hdr:?ELF64_RELA_SIZE/binary, More/binary>> = RelaGC,
  get_safepoint_addresses(More, NumOfEntries-1, [RelaOff|Acc]).


%% @spec get_sdesc_list( binary() ) -> 
%%     [ { {integer() | [], integer(), integer(), {integer()}}, [integer()] } ]
%% @doc The epitome of this module! This function takes an ELF-64 Object File
%%      binary and returns a proper sdesc list for Erlang/OTP System's loader.
%%      The return value should be of the form:
%%        { 
%%          {ExnLabel OR [], FrameSize, StackArity, {Liveroot stack frame indexes}}, 
%%          [Safepoint Addresses] 
%%        }
-spec get_sdesc_list( binary() ) -> 
      [ { {integer() | [], integer(), integer(), {integer()}}, [integer()] } ].
get_sdesc_list(Elf) ->
  %% Extract the needed segments of the object file
  RelaGC = elf64_format:extract_rela(Elf, ?NOTE(?NOTE_ERLGC_NAME)),
  case elf64_format:extract_note(Elf, ?NOTE_ERLGC_NAME) of
    <<>> -> % Object file has no ".note.gc" section!
      [];
    NoteGC ->
      %% Get safe point entries and count 
      {SPCount, SPEntries} = get_safepoint_entries(NoteGC),
      %% Extract information about the safe point addresses
      SPOffs = get_safepoint_addresses(RelaGC, SPCount), % RelaCnt == SPCnt
      %% Extract Exception Handler Labels
      ExnHandlers = elf64_format:get_exn_labels(Elf),
      %% Combine ExnLbls and Safe point addresses (return addresses) properly
      ExnAndSPOffs = combine_ras_and_exns(ExnHandlers, SPOffs),
      %% Do the magic!
      L = get_sdesc_list(SPEntries, ExnAndSPOffs, SPCount, []),
      %% Merge same entries in the list
      elf64_format:flatten_list(L)
  end.

-spec get_sdesc_list( binary(), [{integer(), integer()}], integer(), 
      [ { {integer() | [], integer(), integer(), {integer()}}, integer() } ] ) ->
      [ { {integer() | [], integer(), integer(), {integer()}}, integer() } ].
get_sdesc_list(_SPEntries, _ExnAndSPOffs, 0, Acc) ->
  Acc;
get_sdesc_list(SPEntries, ExnAndSPOffs, NumOfEntries, Acc) ->
  %% Get first SP entry
  SPEntry = get_next_safepoint_entry(SPEntries),
  %% Get information from fixed-size part of a safe point
  FixedSize = get_fixedsize_part(SPEntry),
  StkFrameSize = get_fixedsize_part_field(FixedSize, ?SP_STKFRAME),
  StkArity = get_fixedsize_part_field(FixedSize, ?SP_STKARITY),
  LiveRootCnt = get_fixedsize_part_field(FixedSize, ?SP_LIVEROOTCNT),
  %% Get a tuple with all live roots' stack index
  LiveRootsEntry = get_liveroots_part(SPEntry),
  LiveRoots = get_liveroots(LiveRootsEntry, LiveRootCnt),
  %% Extract exception handler and return (safe point) addresses' offsets in 
  %% code to use in current stack descriptor.
  [{ExnLbl, SPOff} | MoreExnAndSPOffs] = ExnAndSPOffs,
  %% Build current entry for sdesc list and continue with more safepoint 
  %% entries
  SdescEntry = {{ExnLbl, StkFrameSize, StkArity, LiveRoots}, SPOff}, 
  get_sdesc_list(SPEntries, MoreExnAndSPOffs, NumOfEntries-1, 
		 [SdescEntry | Acc]).


%%------------------------------------------------------------------------------
%% Utility functions
%%------------------------------------------------------------------------------

%% @spec combine_ras_and_exns( [{integer(), integer(), integer()}], 
%%                   [integer()] ) -> [{integer() | [], integer()}]
%% @doc 

-spec combine_ras_and_exns( [{integer(), integer(), integer()}], 
			    [integer()] ) 
			  -> [{integer() | [], integer()}].
combine_ras_and_exns(ExnHandlers, RAOffs) ->
  combine_ras_and_exns(ExnHandlers, RAOffs, []).

-spec combine_ras_and_exns( [{integer(), integer(), integer()}], [integer()], 
			    [{integer() | [], integer()}] ) -> 
			    [{integer() | [], integer()}].
combine_ras_and_exns(_, [], Acc) ->
  lists:reverse(Acc);
combine_ras_and_exns(ExnHandlers, [RA | MoreRAs], Acc) ->
  %% FIXME: do something better than O(n^2) by taking advantage of the property
  %% ||ExnHandlers|| <= ||RAs||
  Handler = find_exn_handler(RA, ExnHandlers), 
  combine_ras_and_exns(ExnHandlers, MoreRAs, [{Handler, RA} | Acc]).


%% @spec find_exn_handler( integer(), [{integer(), integer(), integer()}] ) ->
%%			  [] | integer().
%% @doc

-spec find_exn_handler( integer(), [{integer(), integer(), integer()}] ) ->
			  [] | integer().
find_exn_handler(_, []) ->
  [];
find_exn_handler(RA, [{Start, End, Handler} | MoreExnHandlers]) ->
  case (RA >= Start andalso RA =< End) of
    true ->
      Handler;
    false ->
      find_exn_handler(RA, MoreExnHandlers)
  end.
