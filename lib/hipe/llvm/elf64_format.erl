%% -*- erlang-indent-level: 2 -*-
%%% Copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%% Chris Stavrakakis <hydralisk.r@gmail.com>
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
%%% along with Foobar.  If not, see <http://www.gnu.org/licenses/>.

%%% @copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%% Chris Stavrakakis <hydralisk.r@gmail.com>
%%% @version {@version}
%%% @author Yiannis Tsiouris <yiannis.tsiouris@gmail.com>

%%% @doc This module contains functions for extracting various information from
%%% an ELF-64 formated Object file. To fully understand the ELF-64 format and 
%%% the use of these functions please read 
%%% "[http://www.linuxjournal.com/article/1060?page=0,0]" carefully. I warned 
%%% you! :)
-module(elf64_format).

-export([
	 %% Useful functions
	 open_object_file/1, 
	 get_binary_segment/2,
	 extract_segment_by_name/2,
	 %%
	 %% Extract information from ELF-64 Object File Format
	 %%
	 %% File Header
	 extract_header/1, 
	 get_header_field/2,
	 %% Section Header Table
	 extract_shdrtab/1,
	 get_shdrtab_entry/3,
	 get_shdrtab_entry_by_name/2,
	 get_shdrtab_entry_field/2,
	 %% Symbol Table
	 extract_symtab/1,
	 get_symtab_entry/3,
	 get_symtab_entry_field/2,
	 %% String Table
	 extract_strtab/1,
	 get_strtab_subfield/2,
	 %% Relocations
	 extract_rela/2,
	 get_rela_entry/3,
	 get_rela_entry_field/2,
	 get_call_list/1,
	 %% Executable code
	 extract_text/1
	]).

-include("elf64_format.hrl").


%% @spec open_object_file( string() ) -> binary()
%% @doc A function that opens a file as binary. The function takes as argument 
%%      the name of the file and returns an (erlang) binary.

-spec open_object_file( string() ) -> binary().
open_object_file(ObjFile) ->
  Bin = 
    case file:read_file(ObjFile) of
      {ok, Binary} ->
	Binary;
      {error, Reason} -> 
	exit({?MODULE, open_file, Reason})
    end,
  Bin.


%% @spec get_binary_segment( binary(), {integer(), integer()} ) -> binary()
%% @doc Returns the binary segment starting at Offset with length Size (bytes)
%%      from a binary file. If Offset is bigger than the byte size of the ELF-64
%%      binary, an empty binary is returned.

-spec get_binary_segment( binary(), {integer(), integer()} ) -> binary().
get_binary_segment(Elf, {Offset, _Size}) when Offset > byte_size(Elf) ->
  <<>>;
get_binary_segment(Elf, {Offset, Size}) ->
  <<_Hdr:Offset/binary, Bin:Size/binary, _More/binary>> = Elf,
  Bin.


%% @spec extract_segment_by_name( binary(), string() ) -> binary()
%% @doc This function gets as arguments an ELF-64 formated binary object and
%%      a string with the segments' name and returns the specified segment of the
%%      binary or an empty binary (<<>>) if there exists no segment with that
%%      name. There are handy macros defined in elf64_format.hrl for all Standar 
%%      Section Names.

-spec extract_segment_by_name( binary(), string() ) -> binary().
extract_segment_by_name(Elf, Segment) -> 
  SHTEntry = get_shdrtab_entry_by_name(Elf, Segment),
  case (byte_size(SHTEntry) > 0) of
    true -> 
      Offset   = get_shdrtab_entry_field(SHTEntry, ?SH_OFFSET),
      Size     = get_shdrtab_entry_field(SHTEntry, ?SH_SIZE),
      get_binary_segment(Elf, {Offset, Size});
    false ->
      <<>>
  end.


%%------------------------------------------------------------------------------
%% Functions to manipulate ELF-64 File Header
%%------------------------------------------------------------------------------

%% @spec extract_header( binary() ) -> binary()
%% @doc Extracts the File Header from an ELF-64 formated Object file.

-spec extract_header( binary() ) -> binary().
extract_header(Elf) ->
  get_binary_segment(Elf, {0, ?ELF64_EHDR_SIZE}).


%% @spec get_header_field( binary(), {integer(), integer()} ) -> 
%%                           binary() | integer()
%% @doc Extracts information from an ELF-64 File Header. This function takes
%%      as arguments: a FileHeader binary and a tuple of {Size, Offset} (see 
%%      elf64_format.hrl for very handy macros!) and returns a <b>binary</b> when
%%      e_ident information is requested or else an <b>integer</b> with the value
%%      of the field.

-spec get_header_field( binary(), {integer(), integer()} ) -> 
			  binary() | integer().
get_header_field(FileHeader, ?E_IDENT) ->
  get_field(FileHeader, {binary, {?E_IDENT_OFFSET, ?E_IDENT_SIZE}});
get_header_field(FileHeader, {FieldOffset, FieldSize}) ->
  get_field(FileHeader, {integer, {FieldOffset, FieldSize}}).


%%------------------------------------------------------------------------------
%% Functions to manipulate Section Header Entries
%%------------------------------------------------------------------------------

%% @spec extract_shdrtab( binary() ) -> binary()
%% @doc Extracts the Section Header Table from an ELF-64 formated Object File.

-spec extract_shdrtab( binary() ) -> binary().
extract_shdrtab(Elf) ->
  %% Extract File Header binary (to gain info from)
  FileHeader = extract_header(Elf),
  %% Get Section Header Offset (in bytes), Entry Size (in bytes) and Number of
  %% entries
  ShOff     = get_header_field(FileHeader, ?E_SHOFF),
  ShEntsize = get_header_field(FileHeader, ?E_SHENTSIZE),
  ShNum     = get_header_field(FileHeader, ?E_SHNUM),
  %% Compute Size of Section Header Table (in bytes)
  SizeOfSHTable = ShNum * ShEntsize,
  get_binary_segment(Elf, {ShOff, SizeOfSHTable}).


%% @spec get_shdrtab_entry( binary(), integer(), integer() ) -> binary()
%% @doc Extracts a specific Entry of a Section Header Table. This function
%%      takes as argument the Section Header Table (SHdrTab) and the size of an
%%      entry (EntrySize) along with the entry's serial number (EntryNum) and 
%%      returns the entry in binary.  

-spec get_shdrtab_entry( binary(), integer(), integer() ) -> binary().
get_shdrtab_entry(SHdrTab, EntrySize, EntryNum) -> 
  EntryOffset = EntrySize * EntryNum,
  get_field(SHdrTab, {binary, {EntryOffset, EntrySize}}).


%% @spec get_shdrtab_entry_by_name( binary(), string() ) -> binary()
%% @doc Returns the Section Header Table entry with requested name or an empty
%%      binary if no such entry exists.

-spec get_shdrtab_entry_by_name( binary(), string() ) -> binary().
get_shdrtab_entry_by_name(Elf, EntryName) ->
  %% Extract Section Name String Table index and number of entries in Section 
  %% Header Table from File Header.
  FileHeader = extract_header(Elf),
  ShStrNdx   = get_header_field(FileHeader, ?E_SHSTRNDX),
  ShNum      = get_header_field(FileHeader, ?E_SHNUM),
  %% Extract Section Header Table from binary
  SHdrTable  = extract_shdrtab(Elf),
  %% Extract String Name Table from binary
  ShStrSHTEntry = get_shdrtab_entry(SHdrTable, ?ELF64_SHDRENTRY_SIZE, ShStrNdx),
  ShStrOffset   = get_shdrtab_entry_field(ShStrSHTEntry, ?SH_OFFSET),
  ShStrSize     = get_shdrtab_entry_field(ShStrSHTEntry, ?SH_SIZE),
  ShStr         = get_binary_segment(Elf, {ShStrOffset, ShStrSize}),
  %% Find Section Header Table entry by name
  get_shdrtab_entry_by_name(SHdrTable, ShNum, ShStr, EntryName, 0).

-spec get_shdrtab_entry_by_name( binary(), integer(), binary(), string(),
				 integer() ) -> binary().
get_shdrtab_entry_by_name(_SHdrTable, Shnum, _ShStr, _EntryName, Index) 
  when Index >= Shnum ->
  <<>>; % Iterated Shnum entries and couldn't find an entry with EntryName.
get_shdrtab_entry_by_name(SHdrTable, Shnum, ShStr, EntryName, Index) ->
  %% Extract next Section Header Table entry 
  SHeader = get_shdrtab_entry(SHdrTable, ?ELF64_SHDRENTRY_SIZE, Index),
  %% Get offset in String Name Table
  ShName  = get_header_field(SHeader, ?SH_NAME),
  %% Extract Names from String Name Table starting at offset ShName  
  <<_Hdr:ShName/binary, Names/binary>> = ShStr,
  Name = bin_get_string(Names),
  case (EntryName =:= Name) of 
    true -> 
      SHeader;
    false ->
      get_shdrtab_entry_by_name(SHdrTable, Shnum, ShStr, EntryName, Index+1)
  end.

  
%% @spec get_shdrtab_entry_field( binary(), {integer(), integer()} ) -> integer()
%% @doc Extracts information from a Section entry of a Section Entry Table. The
%%      function takes as arguments the Section Header Table (SHdrTab) and a 
%%      tuple of {Offset, Size} of the wanted field (see elf64_format.hrl for 
%%      very very very useful macros!).

-spec get_shdrtab_entry_field( binary(), {integer(), integer()} ) -> integer().
get_shdrtab_entry_field(SHdrEntry, {FieldOffset, FieldSize}) ->
  get_field(SHdrEntry, {integer, {FieldOffset, FieldSize}}).
  

%%------------------------------------------------------------------------------
%% Functions to manipulate Symbol Table
%%------------------------------------------------------------------------------


%% @spec extract_symtab( binary() ) -> binary()
%% @doc Function that extracts Symbol Table from an ELF-64 Object file.

-spec extract_symtab( binary() ) -> binary().
extract_symtab(Elf) ->
  extract_segment_by_name(Elf, ?SYMTAB).


%% @spec get_symtab_entry( binary(), integer(), integer() ) -> binary()
%% @doc Extracts a specific entry from the Symbol Table (as binary). This 
%%      function takes as arguments the Symbol Table (SymTab), the size of a 
%%      Symbol Table entry and the serial number (counting from zero) of a 
%%      specific entry and returns that entry as binary.

-spec get_symtab_entry( binary(), integer(), integer() ) -> binary().
get_symtab_entry(SymTab, EntrySize, EntryNum) -> 
  EntryOffset = EntrySize * EntryNum,
  get_field(SymTab, {binary, {EntryOffset, EntrySize}}).


%% @spec get_symtab_entry_field( binary(), {integer(), integer()} ) -> integer() 
%% @doc Extracts specific field from a Symbol Table entry binary. The function
%%      takes as its arguments a Symbol Table entry binary and a tuple of the 
%%      form {FieldOffset, FieldSize} with the offset inside the binary and the 
%%      size of the wanted field and returns that field's value.

-spec get_symtab_entry_field( binary(), {integer(), integer()} ) -> integer().
get_symtab_entry_field(SymTabEntry, {FieldOffset, FieldSize}) -> 
  get_field(SymTabEntry, {integer, {FieldOffset, FieldSize}}).


%%------------------------------------------------------------------------------
%% Functions to manipulate String Table
%%------------------------------------------------------------------------------

%% @spec extract_strtab( binary() ) -> binary()
%% @doc Extracts String Table from an ELF-64 formated Object File.

-spec extract_strtab( binary() ) -> binary().
extract_strtab(Elf) ->
  extract_segment_by_name(Elf, ?STRTAB).


%% @spec get_strtab_subfield( binary(), integer() ) -> binary()
%% @doc Extracts a part of a String Table binary. The function takes as arguments
%%      a String Table binary (StrTab) and an Offset and returns the sub-binary
%%      starting at that offset.

-spec get_strtab_subfield( binary(), integer() ) -> binary().
get_strtab_subfield(StrTab, Offset) -> 
  Size = byte_size(StrTab) - Offset,
  get_field(StrTab, {binary, {Offset, Size}}).


%%------------------------------------------------------------------------------
%% Functions to manipulate Relocations
%%------------------------------------------------------------------------------

%% @spec extract_rela( binary(), string() ) -> binary()
%% @doc Extract the Relocations segment for section "Name" (that is passed as 
%%      second argument) from an ELF-64 formated Object file binary.

-spec extract_rela( binary(), string() ) -> binary().
extract_rela(Elf, Name) ->
  extract_segment_by_name(Elf, ?RELA(Name)).


%% @spec get_rela_entry( binary(), integer(), integer() ) -> binary()
%% @doc

-spec get_rela_entry( binary(), integer(), integer() ) -> binary().
get_rela_entry(Rela, EntrySize, EntryNum) ->
  EntryOffset = EntrySize * EntryNum,
  get_field(Rela, {binary, {EntryOffset, EntrySize}}). 


%% @spec get_rela_entry_field( binary(), {integer(), integer()} ) -> integer()
%% @ doc

-spec get_rela_entry_field( binary(), {integer(), integer()} ) -> integer().
get_rela_entry_field(Relocations, {FieldOffset, FieldSize}) -> 
  get_field(Relocations, {integer, {FieldOffset, FieldSize}}).


%% @spec get_call_list( binary() ) -> [ {string(), [integer()]} ]
%% @doc

-spec get_call_list( binary() ) -> [ {string(), [integer()]} ].
get_call_list(Elf) ->
  %% 
  SymTab = extract_symtab(Elf),
  StrTab = extract_strtab(Elf),
  Rela   = extract_rela(Elf, ?TEXT),
  %%
  NumOfEntries = byte_size(Rela) div ?ELF64_RELA_SIZE,
  L = get_call_list(SymTab, StrTab, Rela, NumOfEntries, []),
  flatten_call_list(L).

-spec get_call_list( binary(), binary(), binary(), integer(), 
		     [{string(), integer()}] ) -> [{string(), integer()}].
get_call_list(_SymTab, _StrTab, _Rela, 0, Acc) ->
  Acc;
get_call_list(SymTab, StrTab, Rela, N, Acc) ->
  %% Get Offset and Information about name
  Offset   = get_rela_entry_field(Rela, ?R_OFFSET),
  Info     = get_rela_entry_field(Rela, ?R_INFO),
  SymIndex = ?ELF64_R_SYM(Info),
  %% Get name (offset) from Symbol Table
  SymTabEntry = get_symtab_entry(SymTab, ?ELF64_SYM_SIZE, SymIndex),
  SymName     = get_symtab_entry_field(SymTabEntry, ?ST_NAME),
  %% Get name from String Table
  <<_Hdr:SymName/binary, Names/binary>> = StrTab,
  FunctionName = bin_get_string(Names),
  %% Continue with next entries in Relocation "table"
  <<_Head:?ELF64_RELA_SIZE/binary, More/binary>> = Rela,
  get_call_list(SymTab, StrTab, More, N-1, [{FunctionName, Offset} | Acc]).
  

%%------------------------------------------------------------------------------
%% Functions to manipulate Executable Code segment
%%------------------------------------------------------------------------------

%% @spec extract_text( binary() ) -> binary()
%% @doc This function gets as arguments an ELF64 formated binary file and 
%%      returns the Executable Code (".text" segment) or an empty binary if it
%%      is not found.

-spec extract_text( binary() ) -> binary().
extract_text(Elf) ->
  extract_segment_by_name(Elf, ?TEXT).


%%------------------------------------------------------------------------------
%% Utility functions
%%------------------------------------------------------------------------------

%% @spec get_field( binary(), {atom(), {integer(), integer()}} ) -> 
%%                         integer() | binary()
%% @doc

-spec get_field( binary(), {atom(), {integer(), integer()}} ) -> 
		   integer() | binary().
get_field(BinSegment, {integer, {Offset, Size}}) ->
  Bits = ?bits(Size),
  <<_Hdr:Offset/binary, Field:Bits/integer-little, _More/binary>> = BinSegment,
  Field;
get_field(BinSegment, {binary, {Offset, Size}}) ->
  get_binary_segment(BinSegment, {Offset, Size}).


%% @spec bin_reverse( binary() ) -> binary()
%% @doc A function that byte-reverses a binary. This is needed because of little
%%      (fucking!) endianess.

-spec bin_reverse( binary() ) -> binary().
bin_reverse(Bin) when is_binary(Bin) ->
  bin_reverse(Bin, <<>>).

-spec bin_reverse( binary(), binary() ) -> binary().
bin_reverse(<<>>, Acc) ->
  Acc;
bin_reverse(<<Head, More/binary>>, Acc) ->
  bin_reverse(More, << Head, Acc/binary>>).


%% @spec bin_get_string( binary() ) -> string()
%% @doc A function that extracts a null-terminated string from a binary. It 
%%      returns the <b>first</b> string that finds!

-spec bin_get_string( binary() ) -> string().
bin_get_string(Bin) ->
  bin_get_string(Bin, <<>>).

-spec bin_get_string( binary(), binary() ) -> binary().
bin_get_string(<<>>, BinAcc) ->
  %% In case of no lists module found! (not loaded yet)
  %% [ bin_reverse(Name) || Name <- Acc ]
  Bin = bin_reverse(BinAcc), % little endian!
  binary_to_list(Bin);
bin_get_string(<<0, _Tail/binary>>, BinAcc) ->
  Bin = bin_reverse(BinAcc), % little endian!
  binary_to_list(Bin);
bin_get_string(<<Letter, Tail/binary>>, BinAcc) ->
  bin_get_string(Tail, <<Letter, BinAcc/binary>>).


%% @spec flatten_call_list( [{ string(), integer() }] ) -> 
%%			   [{ string(), [integer()] }]
%% @doc 

-spec flatten_call_list( [{ string(), integer() }] ) -> 
			   [{ string(), [integer()] }].
flatten_call_list(L) ->
  L1 = lists:keysort(1,L),
  L2 = lists:foldl(fun flatten_call_list/2 , [], L1),
  L2.

-spec flatten_call_list( [{ string(), integer() }], [{ string(), [integer()] }] ) -> 
			   [{ string(), [integer()] }].
flatten_call_list({Fun, Off}, []) ->
  [{Fun, [Off]}];
flatten_call_list({Fun, Off}, [{PrevFun,Offs} | T]) ->
  case Fun == PrevFun of
    true ->
      [{PrevFun, [Off|Offs]} | T];
    false ->
      [{Fun, [Off]}, {PrevFun, Offs} | T]
  end.