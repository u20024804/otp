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
%%% along with elf64_format.  If not, see <http://www.gnu.org/licenses/>.

%%% @copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%%                      Chris Stavrakakis <hydralisk.r@gmail.com>
%%% @version {@version}
%%% @author Yiannis Tsiouris <yiannis.tsiouris@gmail.com>

%%% @doc This module contains functions for extracting various information from
%%%      an ELF-64 formated Object file. To fully understand the ELF-64 format
%%%      and the use of these functions please read 
%%%      "[http://www.linuxjournal.com/article/1060?page=0,0]" carefully. I
%%%      warned you! :)
-module(elf64_format).

-export([
	 %% Useful functions
	 open_object_file/1, 
	 get_binary_segment/2,
	 extract_segment_by_name/2,
	 get_field/2,
	 flatten_list/1,
	 leb128_decode/1,
	 %%
	 %% Extract information from ELF-64 Object File Format
	 %%
	 %% File Header
	 extract_header/1, 
	 get_header_field/2,
	 %% Section Header Table
	 extract_shdrtab/1,
	 extract_shstrtab/1, % Section Header String Table
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
	 %% Note
	 extract_note/2,
	 %% Executable code
	 extract_text/1,
	 %% GCC Exception Table
	 extract_gcc_exn_table/1,
	 get_gcc_exn_table_info/1,
	 get_exn_labels/1,
	 %% RO Data (constants, labels etc.)
	 extract_rodata/1,
	 get_label_list/1
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
%% @doc Returns the binary segment starting at `Offset' with length `Size' 
%%      (bytes) from a binary file. If `Offset' is bigger than the byte size of
%%      the binary, an empty binary is returned.

-spec get_binary_segment( binary(), {integer(), integer()} ) -> binary().
get_binary_segment(Bin, {Offset, _Size}) when Offset > byte_size(Bin) ->
  <<>>;
get_binary_segment(Bin, {Offset, Size}) ->
  <<_Hdr:Offset/binary, BinSeg:Size/binary, _More/binary>> = Bin,
  BinSeg.


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
%%      as arguments: a `FileHeader' binary and a tuple of {`Size', `Offset'}
%%      (see  elf64_format.hrl for very handy macros!) and returns a
%%      <b>binary</b> when e_ident information is requested or else an
%%      <b>integer</b> with the value of the field.

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


%% @spec extract_shstrtab( binary() ) -> binary()
%% @doc Extracts the Section Header String Table. This section is not a known
%%      ELF64 Object File section. It is just a "hidden" table storing the
%%      names of all sections that exist in current object file.

-spec extract_shstrtab( binary() ) -> binary().
extract_shstrtab(Elf) ->
  %% Extract Section Name String Table index
  FileHeader = extract_header(Elf),
  ShStrNdx   = get_header_field(FileHeader, ?E_SHSTRNDX),
  %% Extract Section Header Table from binary
  SHdrTable  = extract_shdrtab(Elf),
  %% Extract the actual Section Header String Name Table from binary (not a
  %% known section! Usualy located near the end of the object file.)
  ShStrSHTEntry = get_shdrtab_entry(SHdrTable, ?ELF64_SHDRENTRY_SIZE, ShStrNdx),
  ShStrOffset   = get_shdrtab_entry_field(ShStrSHTEntry, ?SH_OFFSET),
  ShStrSize     = get_shdrtab_entry_field(ShStrSHTEntry, ?SH_SIZE),
  get_binary_segment(Elf, {ShStrOffset, ShStrSize}).


%% @spec get_shdrtab_entry( binary(), integer(), integer() ) -> binary()
%% @doc Extracts a specific Entry of a Section Header Table. This function
%%      takes as argument the Section Header Table (`SHdrTab') and the size of
%%      an entry (`EntrySize') along with the entry's serial number (`EntryNum')
%%      and returns the entry in binary.  

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
  ShNum      = get_header_field(FileHeader, ?E_SHNUM),
  %% Extract Section Header Table and Section Header String Table from binary
  SHdrTable  = extract_shdrtab(Elf),
  ShStrTab   = extract_shstrtab(Elf),
  %% Find Section Header Table entry by name
  get_shdrtab_entry_by_name(SHdrTable, ShNum, ShStrTab, EntryName, 0).

-spec get_shdrtab_entry_by_name( binary(), integer(), binary(), string(),
				 integer() ) -> binary().
get_shdrtab_entry_by_name(_SHdrTable, Shnum, _ShStrTab, _EntryName, Index)
  when Index >= Shnum ->
  <<>>; % Iterated Shnum entries and couldn't find an entry with EntryName.
get_shdrtab_entry_by_name(SHdrTable, Shnum, ShStrTab, EntryName, Index) ->
  %% Extract next Section Header Table entry 
  SHeader = get_shdrtab_entry(SHdrTable, ?ELF64_SHDRENTRY_SIZE, Index),
  %% Get offset in String Name Table
  ShName  = get_header_field(SHeader, ?SH_NAME),
  %% Extract Names from String Name Table starting at offset ShName  
  <<_Hdr:ShName/binary, Names/binary>> = ShStrTab,
  Name = bin_get_string(Names),
  case (EntryName =:= Name) of 
    true -> 
      SHeader;
    false ->
      get_shdrtab_entry_by_name(SHdrTable, Shnum, ShStrTab, EntryName, Index+1)
  end.

  
%% @spec get_shdrtab_entry_field( binary(), {integer(), integer()} ) -> 
%%                integer()
%% @doc Extracts information from a Section entry of a Section Entry Table. The
%%      function takes as arguments the Section Header Table (`SHdrTab') and a 
%%      tuple of `{Offset, Size}' of the wanted field (see elf64_format.hrl for 
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
%%      function takes as arguments the Symbol Table (`SymTab'), the size of a
%%      Symbol Table entry and the serial number (counting from zero) of a 
%%      specific entry and returns that entry as binary.

-spec get_symtab_entry( binary(), integer(), integer() ) -> binary().
get_symtab_entry(SymTab, EntrySize, EntryNum) -> 
  EntryOffset = EntrySize * EntryNum,
  get_field(SymTab, {binary, {EntryOffset, EntrySize}}).


%% @spec get_symtab_entry_field( binary(), {integer(), integer()} ) -> integer()
%% @doc Extracts specific field from a Symbol Table entry binary. The function
%%      takes as its arguments a Symbol Table entry binary and a tuple of the 
%%      form {`FieldOffset', `FieldSize'} with the offset inside the binary and
%%      the size of the wanted field and returns that field's value.

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
%%      a String Table binary (`StrTab') and an `Offset' and returns the
%%      sub-binary starting at that offset.

-spec get_strtab_subfield( binary(), integer() ) -> binary().
get_strtab_subfield(StrTab, Offset) -> 
  Size = byte_size(StrTab) - Offset,
  get_field(StrTab, {binary, {Offset, Size}}).


%%------------------------------------------------------------------------------
%% Functions to manipulate Relocations
%%------------------------------------------------------------------------------

%% @spec extract_rela( binary(), string() ) -> binary()
%% @doc Extract the Relocations segment for section `Name' (that is passed as 
%%      second argument) from an ELF-64 formated Object file binary.

-spec extract_rela( binary(), string() ) -> binary().
extract_rela(Elf, Name) ->
  extract_segment_by_name(Elf, ?RELA(Name)).


%% @spec get_rela_entry( binary(), integer(), integer() ) -> binary()
%% @doc Extract the `EntryNum' (serial number) Reloacation Entry of fixed-size
%%      `EntrySize'. Returns a binary.

-spec get_rela_entry( binary(), integer(), integer() ) -> binary().
get_rela_entry(Rela, EntrySize, EntryNum) ->
  EntryOffset = EntrySize * EntryNum,
  get_field(Rela, {binary, {EntryOffset, EntrySize}}). 


%% @spec get_rela_entry_field( binary(), {integer(), integer()} ) -> integer()
%% @ doc Extract a specific field `{FieldOffset, FieldSize}' of a `Relocation'
%%       entry.

-spec get_rela_entry_field( binary(), {integer(), integer()} ) -> integer().
get_rela_entry_field(Relocation, {FieldOffset, FieldSize}) -> 
  get_field(Relocation, {integer, {FieldOffset, FieldSize}}).


%% @spec get_call_list( binary() ) -> [ {string(), [integer()]} ]
%% @doc Create a call list of the form `[ {FunName, [Offset]} ]` with all 
%%      Function names and offsets of the calls in the binary. Very useful in
%%      many cases that you might want to extract that kind of information from
%%      an object file.

-spec get_call_list( binary() ) -> [ {string(), [integer()]} ].
get_call_list(Elf) ->
  %% Extract Symbol, String and Relocation Tables
  Rela   = extract_rela(Elf, ?TEXT), % All calls are Relocatable data indexing
				     %   Symbol Table
  SymTab = extract_symtab(Elf),      % Holds the offsets in Str Table of all 
				     %   symbols
  StrTab = extract_strtab(Elf),      % Str Table holds all symbols' string names
  %% But we *also* need (in case of a section header index in R_SYM):
  SHdrTab = extract_shdrtab(Elf),    % Section Header Table
  ShStrTab= extract_shstrtab(Elf),   % Section Header string table (not apparent
				     %   even with readelf!)
  %% Do the magic!
  NumOfEntries = byte_size(Rela) div ?ELF64_RELA_SIZE,
  L = get_call_list(SymTab, StrTab, SHdrTab, ShStrTab, Rela, NumOfEntries, []),
  %% Merge identical function calls to one tuple and a list of offsets
  flatten_list(L).

-spec get_call_list( binary(), binary(), binary(), binary(), binary(), integer(),
		     [{string(), integer()}] ) -> [{string(), integer()}].
%% XXX: Maybe iterate on Rela binary (get rid of N).
get_call_list(_SymTab, _StrTab, _SHdrTab, _ShStrTab, _Rela, 0, Acc) ->
  Acc;
get_call_list(SymTab, StrTab, SHdrTab, ShStrTab, Rela, N, Acc) ->
  %% Get Offset and Information about name
  Offset   = get_rela_entry_field(Rela, ?R_OFFSET),
  Info     = get_rela_entry_field(Rela, ?R_INFO),
  SymIndex = ?ELF64_R_SYM(Info),
  %% Get name (offset) from Symbol Table
  SymTabEntry = get_symtab_entry(SymTab, ?ELF64_SYM_SIZE, SymIndex),
  Shndx       = get_symtab_entry_field(SymTabEntry, ?ST_SHNDX),
  SymName     = get_symtab_entry_field(SymTabEntry, ?ST_NAME),
  %% Extract symbol's name
  FunctionName =
    case Shndx of
      ?SHN_UNDEF -> %% Get name from String Table (undefined symbol)
	<<_Hdr:SymName/binary, Names/binary>> = StrTab,
	bin_get_string(Names);
      Ni -> %% Get name from Section Header Table (name of section)
	SHeader = get_shdrtab_entry(SHdrTab, ?ELF64_SHDRENTRY_SIZE, Ni),
	ShName = get_header_field(SHeader, ?SH_NAME),
	<<_Hdr:ShName/binary, Names2/binary>> = ShStrTab,
	bin_get_string(Names2)
    end,
  %% Continue with next entries in Relocation "table"
  <<_Head:?ELF64_RELA_SIZE/binary, More/binary>> = Rela,
  get_call_list(SymTab, StrTab, SHdrTab, ShStrTab, More, N-1,
		[{FunctionName, Offset} | Acc]).
  

%%------------------------------------------------------------------------------
%% Functions to manipulate Note Section
%%------------------------------------------------------------------------------

%% @spec extract_note( binary(), string() ) -> binary()
%% @doc Extract specific Note Section from an ELF-64 Object file. The function
%%      takes as first argument the object file (`Elf') and the `Name' of the
%%      wanted Note Section (<b>without</b> the ".note." prefix!). It returns
%%      the specified binary segment or an empty binary if no such section 
%%      exists.
-spec extract_note( binary(), string() ) -> binary().
extract_note(Elf, Name) ->
  extract_segment_by_name(Elf, ?NOTE(Name)).


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
%% Functions to manipulate GCC Exception Table segment
%%------------------------------------------------------------------------------

%% A description for the C++ exception table formats can be found at Exception
%% Handling Tables (http://www.codesourcery.com/cxx-abi/exceptions.pdf).

%% @spec extract_gcc_exn_table( binary() ) -> binary()
%% @doc This function gets as argument an ELF64 binary file and returns the
%%      GCC Exception Table (".gcc_except_table") section or an empty binary if
%%      it is not found.

-spec extract_gcc_exn_table( binary() ) -> binary().
extract_gcc_exn_table(Elf) ->
  extract_segment_by_name(Elf, ?GCC_EXN_TAB).


%% @spec get_gcc_exn_table_info( binary() ) -> binary()
%% @doc 

-spec get_gcc_exn_table_info( binary() ) -> binary().
get_gcc_exn_table_info(GCCExnTab) ->
  %% First byte of LSDA is Landing Pad base encoding.
  <<LBenc:8, More/binary>> = GCCExnTab,
  %% Second byte is the Landing Pad base (if it encoding is note DW_EH_PE_omit).
  {LPBase, LSDACont} = 
    case LBenc == ?DW_EH_PE_omit of
      true ->  % No landing pad base byte.
	{0, More};
      false -> % Landing pad base.
	<<Base:8, More2/binary>> = More,
	{Base, More2}
    end,
  %% Third byte of LSDA is the encoding of the Type Table.
  <<TTenc:8, More3/binary>> = LSDACont,
  %% Forth byte is the Types Table offset encoded in U-LEB128 (if it exists).
  {TTOff, LSDACont2} =
    case TTenc == ?DW_EH_PE_omit of
      true ->  % There is no Types Table pointer.
	{0, More3};
      false -> % The byte offset from this field to the start of the Types Table
	       % used for exception matching.
	leb128_decode(More3)
    end,
  %% Fifth byte of LSDA is the encoding of the fields in the Call-site Table.
  <<CSenc:8, More4/binary>> = LSDACont2,
  %% Sixth byte is the size (in bytes) of the Call-site Table encoded in 
  %% U-LEB128.
  leb128_decode(More4).
  

%% @spec get_exn_labels( binary() ) -> [{integer(), integer(), integer()}]
%% @doc Extracts a list with {`Start', `End', `HandlerOffset'} for all Exception
%%      Handlers that appear in the code.
	 
-spec get_exn_labels( binary() ) -> [{integer(), integer(), integer()}].
get_exn_labels(Elf) ->
  %% Extract the GCC Exception Table
  case extract_gcc_exn_table(Elf) of
    <<>> -> % There is no .gcc_except_table section in object file.
      [];
    GCCExnTab -> 
      %% Extract information about Call-site Table
      {CSTabSize, CSTab} = get_gcc_exn_table_info(GCCExnTab),
      %% Extract the Exception labels list
      get_exn_labels(CSTab, CSTabSize, [])
  end.

-spec get_exn_labels( binary(), integer(), [{integer(), integer()}] ) -> 
			[{integer(), integer(), integer()}].
get_exn_labels(_CSTab, 0, Acc) ->
  lists:reverse(Acc);
get_exn_labels(CSTab, CSTabSize, Acc) ->
  %% We are only interested in the Landing pad of every entry.
  <<Start:32/integer-little, Length:32/integer-little, 
    LP:32/integer-little, _Act:8, More/binary>> = CSTab,
  case LP == 0 of
    true -> % Not interested in that call-site (FIXME: Hardcoded entry size!).
      get_exn_labels(More, CSTabSize-13, Acc);
    false -> % Store LP of current call-site and continue.
      get_exn_labels(More, CSTabSize-13, [ {Start, Start+Length, LP} | Acc])
  end.
			        

%%------------------------------------------------------------------------------
%% Functions to manipulate .rodata Section
%%------------------------------------------------------------------------------

%% @spec extract_rodata( binary() ) -> binary()
%% @doc This function gets as argument an ELF64 formated binary file and
%%      returns the Read-only Data (".rodata" segment) or an empty binary if it
%%      is not found.

-spec extract_rodata( binary() ) -> binary().
extract_rodata(Elf) ->
  extract_segment_by_name(Elf, ?RODATA).


%% @spec get_label_list( binary() ) -> [integer()]
%% @doc This function get as argument an ELF64 binary file and returns a list
%%      with all .rela.rodata labels (that is constants and literals in code)
%%      or an empty list if no .rela.rodata section exists in code.

-spec get_label_list( binary() ) -> [integer()].
get_label_list(Elf) ->
  %% Extract relocation entries for .rodata segment
  %Rodata = extract_rodata(Elf),
  case extract_rela(Elf, ?RODATA) of
    <<>> ->
      [];
    RelaRodata ->
      NumOfEntries = byte_size(RelaRodata) div ?ELF64_RELA_SIZE,
      get_label_list(RelaRodata, NumOfEntries, [])
  end.

-spec get_label_list( binary(), integer(), [integer()] ) -> integer().
get_label_list(_RelaRodata, 0, Acc) ->
  lists:reverse(Acc);
get_label_list(RelaRodata, N, Acc) ->
  %% Get relocation entry information
  _Offset = get_rela_entry_field(RelaRodata, ?R_OFFSET),
  _Info = get_rela_entry_field(RelaRodata, ?R_INFO),
  Addend = get_rela_entry_field(RelaRodata, ?R_ADDEND),
  %% Store addend (offset in .text segment) and continue with more entries
  <<_Head:?ELF64_RELA_SIZE/binary, MoreRodata/binary>> = RelaRodata,
  get_label_list(MoreRodata, N-1, [Addend | Acc]).


%%------------------------------------------------------------------------------
%% Utility functions
%%------------------------------------------------------------------------------

%% @spec get_field( binary(), {atom(), {integer(), integer()}} ) -> 
%%                         integer() | binary()
%% @doc Helper function that returns a field of a binary starting at `Offset' 
%%      with size `Size'. It returns either an little-endian integer or a binary
%%      depending on the atom it takes as first element of the tuple (second 
%%      argument). It can easily be extended to return more information such as
%%      big-endian integer, float, bitstring etc.

-spec get_field( binary(), {atom(), {integer(), integer()}} ) -> 
		   integer() | binary().
get_field(BinSegment, {integer, {Offset, Size}}) ->
  Bits = ?bits(Size),
  <<_Hdr:Offset/binary, Field:Bits/integer-little, _More/binary>> = BinSegment,
  Field;
get_field(BinSegment, {binary, {Offset, Size}}) ->
  get_binary_segment(BinSegment, {Offset, Size}).


%% @spec bin_reverse( binary() ) -> binary()
%% @doc A function that byte-reverses a binary. This might be needed because of
%%      little (fucking!) endianess.

-spec bin_reverse( binary() ) -> binary().
bin_reverse(Bin) when is_binary(Bin) ->
  bin_reverse(Bin, <<>>).

-spec bin_reverse( binary(), binary() ) -> binary().
bin_reverse(<<>>, Acc) ->
  Acc;
bin_reverse(<<Head, More/binary>>, Acc) ->
  bin_reverse(More, <<Head, Acc/binary>>).


%% @spec bin_get_string( binary() ) -> string()
%% @doc A function that extracts a null-terminated string from a binary. It 
%%      returns the <b>first</b> string that finds!

-spec bin_get_string( binary() ) -> string().
bin_get_string(Bin) ->
  bin_get_string(Bin, <<>>).

-spec bin_get_string( binary(), binary() ) -> binary().
bin_get_string(<<>>, BinAcc) ->
  %% In case of no lists module found (not loaded yet):
  %%   [ bin_reverse(Name) || Name <- Acc ]
  Bin = bin_reverse(BinAcc), % little endian!
  binary_to_list(Bin);
bin_get_string(<<0, _Tail/binary>>, BinAcc) ->
  Bin = bin_reverse(BinAcc), % little endian!
  binary_to_list(Bin);
bin_get_string(<<Letter, Tail/binary>>, BinAcc) ->
  bin_get_string(Tail, <<Letter, BinAcc/binary>>).


%% @spec flatten_list( [{ atom(), atom() }] ) -> 
%%			   [{ atom(), [atom()] }]
%% @doc Magic function that compacts a list of tuples based on the first 
%%      element of each tuple.

-spec flatten_list( [{ atom(), atom() }] ) -> 
			   [{ atom(), [atom()] }].
flatten_list(L) ->
  %% Sort the list of tuples based on the first element
  L1 = lists:keysort(1,L), 
  %% Fold the list with "compresser" function
  L2 = lists:foldl(fun flatten_list/2 , [], L1),
  L2.

-spec flatten_list( [{ atom(), atom() }], [{ atom(), [atom()] }] ) -> 
			   [{ atom(), [atom()] }].
flatten_list({Key, Val}, []) ->
  [{Key, [Val]}];
flatten_list({Key, Val}, [{PrevKey,Vals} | T]) ->
  case Key == PrevKey of 
    %% If the current key is the same with the prev key in sorted list:
    true ->
      [{PrevKey, [Val|Vals]} | T]; % collapse the values of the key to a list
    %% Else:
    false ->  
      [{Key, [Val]}, {PrevKey, Vals} | T] % just insert the tuple
  end.


%% @spec leb128_decode( binary() ) -> {integer(), binary()}
%% @oc Little-Endian Base 128 (LEB128) Decoder
%%     This function extracts the <b>first</b> LEB128-encoded integer in a 
%%     binary and returns that integer along with the remaining binary. This is
%%     done because a LEB128 number has variable bit-size and that is a way of
%%     extracting only one number in a binary and continuing parsing the binary
%%     for other kind of data (e.g. different encoding). 

% FIXME: Only decodes unsigned data!
-spec leb128_decode( binary() ) -> {integer(), binary()}.
leb128_decode(LebNum) ->
  leb128_decode(LebNum, 0, <<>>).

-spec leb128_decode( binary(), integer(), binary() ) -> {integer(), binary()}.
leb128_decode(LebNum, NoOfBits, Acc) ->
  <<Sentinel:1/bits, NextBundle:7/bits, MoreLebNums/bits>> = LebNum,
  case Sentinel of
    <<1:1>> -> % more bytes to follow
      leb128_decode(MoreLebNums, NoOfBits+7, <<NextBundle:7/bits, Acc/bits>>);
    <<0:1>> -> % byte bundle stop
      Size = NoOfBits+7,
      <<Num:Size/integer>> = <<NextBundle:7/bits, Acc/bits>>,
      {Num, MoreLebNums}
  end.
