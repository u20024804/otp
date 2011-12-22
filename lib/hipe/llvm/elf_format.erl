%% -*- erlang-indent-level: 2 -*-

%%% @copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%%                      Chris Stavrakakis <hydralisk.r@gmail.com>
%%% @author Yiannis Tsiouris <yiannis.tsiouris@gmail.com>
%%%    [http://www.softlab.ntua.gr/~gtsiour/]

%%% @doc This module contains functions for extracting various information from
%%%      an ELF formated Object file. To fully understand the ELF format
%%%      and the use of these functions please read
%%%      "[http://www.linuxjournal.com/article/1060?page=0,0]" carefully. I
%%%      warned you! :)
-module(elf_format).

-export([
	 %% File Header
	 extract_header/1,
	 get_header_field/2,
	 %% Section Header Table
	 extract_shdrtab/1,
	 get_shdrtab_entry/2,
	 get_shdrtab_entry_field/2,
	 %% Section Header String Table
	 extract_shstrtab/1,
	 %% Symbol Table
	 extract_symtab/1,
	 get_symtab_entry/2,
	 get_symtab_entry_field/2,
	 %% String Table
	 extract_strtab/1,
	 get_strtab_entry/2,
	 %% Relocations
	 extract_rela/2,
	 get_rela_entry/2,
	 get_rela_entry_field/2,
	 %% Note
	 extract_note/2,
	 %% Executable code
	 extract_text/1,
	 %% GCC Exception Table
	 extract_gccexntab/1,
	 get_gccexntab_field/2
	]).

-include("elf_format.hrl").
-include("elf_datatypes.hrl").

%%------------------------------------------------------------------------------
%% Functions to manipulate ELF File Header
%%------------------------------------------------------------------------------

%% @doc Extracts the File Header from an ELF formated Object file.
extract_header(Elf) ->
  Ehdr_bin = get_binary_segment(Elf, {0, ?ELF_EHDR_SIZE}),
  << %% Structural patern-matching on fields.
     Ident_bin:?E_IDENT_SIZE/binary,
     Type:?bits(?E_TYPE_SIZE)/integer-little,
     Machine:?bits(?E_MACHINE_SIZE)/integer-little,
     Version:?bits(?E_VERSION_SIZE)/integer-little,
     Entry:?bits(?E_ENTRY_SIZE)/integer-little,
     Phoff:?bits(?E_PHOFF_SIZE)/integer-little,
     Shoff:?bits(?E_SHOFF_SIZE)/integer-little,
     Flags:?bits(?E_FLAGS_SIZE)/integer-little,
     Ehsize:?bits(?E_EHSIZE_SIZE)/integer-little,
     Phentsize:?bits(?E_PHENTSIZE_SIZE)/integer-little,
     Phnum:?bits(?E_PHNUM_SIZE)/integer-little,
     Shentsize:?bits(?E_SHENTSIZE_SIZE)/integer-little,
     Shnum:?bits(?E_SHENTSIZE_SIZE)/integer-little,
     Shstrndx:?bits(?E_SHSTRNDX_SIZE)/integer-little
  >> = Ehdr_bin,
  <<16#7f, $E, $L, $F, EI_Class, EI_Data, EI_Version, EI_Osabi, EI_Abiversion,
    EI_Pad:6/binary, EI_Nident
  >> = Ident_bin,
  Ident = elf_datatypes:mk_ehdr_ident(EI_Class, EI_Data, EI_Version, EI_Osabi,
			      EI_Abiversion, EI_Pad, EI_Nident),
  elf_datatypes:mk_ehdr(Ident, Type, Machine, Version, Entry, Phoff, Shoff,
			Flags, Ehsize, Phentsize, Phnum, Shentsize, Shnum,
			Shstrndx).

%% @doc Extracts information from an ELF File Header. This function takes
%%      as arguments: a `FileHeader' record and a valid `Field' and returns the
%%      value of that field.
get_header_field(Ehdr, Field) ->
  elf_datatypes:ehdr_field(Ehdr, Field).

%%------------------------------------------------------------------------------
%% Functions to manipulate Section Header Entries
%%------------------------------------------------------------------------------

%% @doc Extracts the Section Header Table from an ELF formated Object File.
extract_shdrtab(Elf) ->
  %% Extract File Header binary (to gain info from)
  FileHeader = extract_header(Elf),
  %% Get Section Header Offset (in bytes), Entry Size (in bytes) and Number of
  %% entries
  ShOff     = get_header_field(FileHeader, e_shoff),
  ShEntsize = get_header_field(FileHeader, e_shentsize),
  ShNum     = get_header_field(FileHeader, e_shnum),
  %% Get actual Section header table (binary)
  Shdr_bin  = get_binary_segment(Elf, {ShOff,  ShNum * ShEntsize}),
  get_shdrtab_entries(Shdr_bin, []).

get_shdrtab_entries(<<>>, Acc) ->
  lists:reverse(Acc);
get_shdrtab_entries(Shdr_bin, Acc) ->
  << %% Structural patern-matching on fields.
     Name:?bits(?SH_NAME_SIZE)/integer-little,
     Type:?bits(?SH_TYPE_SIZE)/integer-little,
     Flags:?bits(?SH_FLAGS_SIZE)/integer-little,
     Addr:?bits(?SH_ADDR_SIZE)/integer-little,
     Offset:?bits(?SH_OFFSET_SIZE)/integer-little,
     Size:?bits(?SH_SIZE_SIZE)/integer-little,
     Link:?bits(?SH_LINK_SIZE)/integer-little,
     Info:?bits(?SH_INFO_SIZE)/integer-little,
     Addralign:?bits(?SH_ADDRALIGN_SIZE)/integer-little,
     Entsize:?bits(?SH_ENTSIZE_SIZE)/integer-little,
     MoreShdrE/binary
  >> = Shdr_bin,
  ShdrE = elf_datatypes:mk_shdr(Name, Type, Flags, Addr, Offset,
		      Size, Link, Info, Addralign, Entsize),
  get_shdrtab_entries(MoreShdrE, [ShdrE | Acc]).

%% @doc Extracts a specific Entry of a Section Header Table. This function
%%      takes as argument the Section Header Table (`SHdrTab') and the entry's
%%      serial number (`EntryNum') and returns the entry (`shdr').
get_shdrtab_entry(SHdrTab, EntryNum) ->
  lists:nth(EntryNum + 1, SHdrTab).

%% @doc Extracts information from a Section header entry. The function takes as
%%      arguments the Section header entry and the name of the wanted field
%%      (`atom').
get_shdrtab_entry_field(Shdr, Field) ->
  elf_datatypes:shdr_field(Shdr, Field).

%%------------------------------------------------------------------------------
%% Functions to manipulate Section Header String Table
%%------------------------------------------------------------------------------

%% @doc Extracts the Section Header String Table. This section is not a known
%%      ELF Object File section. It is just a "hidden" table storing the
%%      names of all sections that exist in current object file.
extract_shstrtab(Elf) ->
  %% Extract Section Name String Table index
  FileHeader = extract_header(Elf),
  ShStrNdx   = get_header_field(FileHeader, e_shstrndx),
  ShHdrTab   = extract_shdrtab(Elf),
  %% Extract Section header entry
  Shdr       = get_shdrtab_entry(ShHdrTab, ShStrNdx),
  %% Get actual Section-header String Table
  ShStrOffset = get_shdrtab_entry_field(Shdr, sh_offset),
  ShStrSize   = get_shdrtab_entry_field(Shdr, sh_size),
  ShStrTab    = get_binary_segment(Elf, {ShStrOffset, ShStrSize}),
  %% Convert to string table
  [Name || {Name, _Size} <- get_names(ShStrTab)].

%%------------------------------------------------------------------------------
%% Functions to manipulate Symbol Table
%%------------------------------------------------------------------------------

%% @doc Function that extracts Symbol Table from an ELF Object file.
extract_symtab(Elf) ->
  Symtab_bin = extract_segment_by_name(Elf, ?SYMTAB),
  get_symtab_entries(Symtab_bin, []).

get_symtab_entries(<<>>, Acc) ->
  lists:reverse(Acc);
get_symtab_entries(Symtab_bin, Acc) ->
  << %% Structural patern-matching on fields.
     Name:?bits(?ST_NAME_SIZE)/integer-little,
     Info:?bits(?ST_INFO_SIZE)/integer-little,
     Other:?bits(?ST_OTHER_SIZE)/integer-little,
     Shndx:?bits(?ST_SHNDX_SIZE)/integer-little,
     Value:?bits(?ST_VALUE_SIZE)/integer-little,
     Size:?bits(?ST_SIZE_SIZE)/integer-little,
     MoreSymE/binary
  >> = Symtab_bin,
  SymE = elf_datatypes:mk_sym(Name, Info, Other, Shndx, Value, Size),
  get_symtab_entries(MoreSymE, [SymE | Acc]).

%% @doc Extracts a specific entry from the Symbol Table (as binary). This
%%      function takes as arguments the Symbol Table (`SymTab') and the entry's
%%      serial number and returns that entry (`sym').
get_symtab_entry(SymTab, EntryNum) ->
  lists:nth(EntryNum + 1, SymTab).

%% @doc Extracts specific field from a Symbol Table entry binary. The function
%%      takes as its arguments a Symbol Table entry (`sym') and the name of the
%%      wanted field (`atom') and returns that field's value.
get_symtab_entry_field(Sym, Field) ->
  elf_datatypes:sym_field(Sym, Field).

%%------------------------------------------------------------------------------
%% Functions to manipulate String Table
%%------------------------------------------------------------------------------

%% @doc Extracts String Table from an ELF formated Object File.
-spec extract_strtab( binary() ) -> [ {string(), integer()} ].
extract_strtab(Elf) ->
  Strtab_bin = extract_segment_by_name(Elf, ?STRTAB),
  NamesSizes = get_names(Strtab_bin),
  make_offsets(NamesSizes).

%% @doc Returns the name of the symbol at the given offset. The string table
%%      contains entries of the form {Name, Offset}. If no such offset exists
%%      returns the empty string (`""').
%%      XXX: There might be a bug here because of the "compact" saving the ELF
%%      format uses: e.g. only stores ".rela.text" for ".rela.text" and ".text".
get_strtab_entry(Strtab, Offset) ->
  case lists:keysearch(Offset, 2, Strtab) of
    {value, {Name, Offset}} -> Name;
    false -> ""
  end.

%%------------------------------------------------------------------------------
%% Functions to manipulate Relocations
%%------------------------------------------------------------------------------

%% @doc Extract the Relocations segment for section `Name' (that is passed as
%%      second argument) from an ELF formated Object file binary.
extract_rela(Elf, Name) ->
  Rela_bin = extract_segment_by_name(Elf, ?RELA(Name)),
  get_rela_entries(Rela_bin, []).

get_rela_entries(<<>>, Acc) ->
  lists:reverse(Acc);
get_rela_entries(Rela_bin, Acc) ->
  <<%% Structural patern-matching on fields.
     Offset:?bits(?R_OFFSET_SIZE)/integer-little,
     Info:?bits(?R_INFO_SIZE)/integer-little,
     Addend:?bits(?R_ADDEND_SIZE)/integer-little,
     MoreRelaE/binary
  >> = Rela_bin,
  RelaE = elf_datatypes:mk_rela(Offset, Info, Addend),
  get_rela_entries(MoreRelaE, [RelaE | Acc]).

%% @doc Extract the `EntryNum' (serial number) Reloacation Entry.
get_rela_entry(Rela, EntryNum) ->
  lists:nth(EntryNum + 1, Rela).

%% @ doc Extract a specific field (name is `atom') of a `Relocation' entry.
get_rela_entry_field(RelaE, Field) ->
  elf_datatypes:rela_field(RelaE, Field).

%%------------------------------------------------------------------------------
%% Functions to manipulate Executable Code segment
%%------------------------------------------------------------------------------

%% @doc This function gets as arguments an ELF formated binary file and
%%      returns the Executable Code (".text" segment) or an empty binary if it
%%      is not found.
-spec extract_text( binary() ) -> binary().
extract_text(Elf) ->
  extract_segment_by_name(Elf, ?TEXT).

%%------------------------------------------------------------------------------
%% Functions to manipulate Note Section
%%------------------------------------------------------------------------------

%% @doc Extract specific Note Section from an ELF Object file. The function
%%      takes as first argument the object file (`Elf') and the `Name' of the
%%      wanted Note Section (<b>without</b> the ".note" prefix!). It returns
%%      the specified binary segment or an empty binary if no such section
%%      exists.
-spec extract_note( binary(), string() ) -> binary().
extract_note(Elf, Name) ->
  extract_segment_by_name(Elf, ?NOTE(Name)).

%%------------------------------------------------------------------------------
%% Functions to manipulate GCC Exception Table segment
%%------------------------------------------------------------------------------

%% A description for the C++ exception table formats can be found at Exception
%% Handling Tables (http://www.codesourcery.com/cxx-abi/exceptions.pdf).

%% @doc This function gets as argument an ELF binary file and returns the
%%      GCC Exception Table (".gcc_except_table") section or an empty list if
%%      it is not found.
%%      XXX: Assumes there is *no* Action Record Table.
extract_gccexntab(Elf) ->
  case extract_segment_by_name(Elf, ?GCC_EXN_TAB) of
    <<>> ->
      [];
    Exntab_bin ->
      %% First byte of LSDA is Landing Pad base encoding.
      <<LBenc:8, More/binary>> = Exntab_bin,
      %% Second byte is the Landing Pad base (if it's encoding is not
      %% DW_EH_PE_omit) (optional).
      {LPBase, LSDACont} =
	case LBenc == ?DW_EH_PE_omit of
	  true ->  % No landing pad base byte. (-1 denotes that)
	    {-1, More};
	  false -> % Landing pad base.
	    <<Base:8, More2/binary>> = More,
	    {Base, More2}
	end,
      %% Next byte of LSDA is the encoding of the Type Table.
      <<TTenc:8, More3/binary>> = LSDACont,
      %% Next byte is the Types Table offset encoded in U-LEB128 (optional).
      {TTOff, LSDACont2} =
	case TTenc == ?DW_EH_PE_omit of
	  true ->  % There is no Types Table pointer. (-1 denotes that)
	    {-1, More3};
	  false -> % The byte offset from this field to the start of the Types
		   % Table used for exception matching.
	    leb128_decode(More3)
	end,
      %% Next byte of LSDA is the encoding of the fields in the Call-site Table.
      <<CSenc:8, More4/binary>> = LSDACont2,
      %% Sixth byte is the size (in bytes) of the Call-site Table encoded in
      %% U-LEB128.
      {CSTabSize, CSTable} = leb128_decode(More4),
      %% Extract all call-site information
      GccCallSites = get_gccexntab_callsites(CSTable, []),
      elf_datatypes:mk_gccexntab(LBenc, LPBase, TTenc, TTOff, CSenc, CSTabSize,
				 GccCallSites)
  end.

get_gccexntab_callsites(<<>>, Acc) ->
  lists:reverse(Acc);
get_gccexntab_callsites(CSTab, Acc) ->
  %% We are only interested in the Landing pad of every entry.
  <<Start:32/integer-little, Size:32/integer-little,
    LP:32/integer-little, OnAction:8, More/binary
  >> = CSTab,
  GccCS = elf_datatypes:mk_gccexntab_callsite(Start, Size, LP, OnAction),
  get_gccexntab_callsites(More, [GccCS | Acc]).

%% @ doc Extract a specific field (name is `atom') of a GCC Exception Table.
get_gccexntab_field(Ge, Field) ->
  elf_datatypes:gccexntab_field(Ge, Field).

%%------------------------------------------------------------------------------
%% Helper functions
%%------------------------------------------------------------------------------

%% @doc Returns the binary segment starting at `Offset' with length `Size'
%%      (bytes) from a binary file. If `Offset' is bigger than the byte size of
%%      the binary, an empty binary (`<<>>') is returned.
-spec get_binary_segment( binary(), {integer(), integer()} ) -> binary().
get_binary_segment(Bin, {Offset, _Size}) when Offset > byte_size(Bin) ->
  <<>>;
get_binary_segment(Bin, {Offset, Size}) ->
  <<_Hdr:Offset/binary, BinSeg:Size/binary, _More/binary>> = Bin,
  BinSeg.

%% @doc This function gets as arguments an ELF formated binary object and
%%      a string with the segments' name and returns the specified segment or
%%      an empty binary (`<<>>') if there exists no segment with that name.
%%      There are handy macros defined in elf_format.hrl for all Standar
%%      Section Names.
-spec extract_segment_by_name( binary(), string() ) -> binary().
extract_segment_by_name(Elf, SectionName) ->
  %% Extract Section Header Table and Section Header String Table from binary
  SHdrTable = extract_shdrtab(Elf),
  Names     = extract_shstrtab(Elf),
  %% Zip to a list of (Name,ShdrE)
  [_Zero | ShdrEs] = lists:keysort(2, SHdrTable), % Skip first entry (zeros).
  L = lists:zip(Names, ShdrEs),
  %% Find Section Header Table entry by name
  case lists:keyfind(SectionName, 1, L) of
    {SectionName, ShdrE} -> %% Note: Same name.
      Off = get_shdrtab_entry_field(ShdrE, sh_offset),
      Size = get_shdrtab_entry_field(ShdrE, sh_size),
      get_binary_segment(Elf, {Off, Size});
    false -> %% Not found.
      <<>>
  end.

%% @doc Extracts a list of strings with (zero-separated) names from a binary.
%%      Returns tuples of `{Name, Size}'.
%%      XXX: Skip trailing 0.
-spec get_names( binary() ) -> [ string() ].
get_names(<<0, Bin/binary>>) ->
  NamesSizes = get_names(Bin, []),
  fix_names(NamesSizes, []).

get_names(<<>>, Acc) ->
  lists:reverse(Acc);
get_names(Bin, Acc) ->
  {Name, MoreNames} = bin_get_string(Bin),
  get_names(MoreNames, [{Name, length(Name)} | Acc]).

%% @doc Fix names:
%%      e.g. If ".rela.text" exists, ".text" does not.
%%           In that way, the Section Header String Table is more compact. Add
%            ".text" just *before* the corresponding rela-field, etc.
%%      Currently works only for ".rela" spanned entries.
fix_names([], Acc) ->
  lists:reverse(Acc);
fix_names([{Name, Size}=T | Names], Acc) ->
  case string:str(Name, ".rela") =:= 1 of
    true -> %% Name starts with ".rela":
      Section = string:substr(Name, 6),
      fix_names(Names, [{Section, Size - 5}
			| [T | Acc]]); % XXX: Is order ok? (".text"
						% always before ".rela.text")
    false -> %% Name does not start with ".rela":
      fix_names(Names, [T | Acc])
  end.

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

%% @doc A function that extracts a null-terminated string from a binary. It
%%      returns the found string along with the rest of the binary.
-spec bin_get_string( binary() ) -> {string(), binary() }.
bin_get_string(Bin) ->
  bin_get_string(Bin, <<>>).

bin_get_string(<<>>, BinAcc) ->
  Bin = bin_reverse(BinAcc), % little endian!
  {binary_to_list(Bin), <<>>};
bin_get_string(<<0, MoreBin/binary>>, BinAcc) ->
  Bin = bin_reverse(BinAcc), % little endian!
  {binary_to_list(Bin), MoreBin};
bin_get_string(<<Letter, Tail/binary>>, BinAcc) ->
  bin_get_string(Tail, <<Letter, BinAcc/binary>>).

%% @doc
make_offsets(NamesSizes) ->
    {Names, Sizes} = lists:unzip(NamesSizes),
    Offsets = make_offsets_from_sizes(Sizes, 1, []),
    lists:zip(Names, Offsets).

make_offsets_from_sizes([], _, Acc) ->
    lists:reverse(Acc);
make_offsets_from_sizes([Size | Sizes], Cur, Acc) ->
    make_offsets_from_sizes(Sizes, Size+Cur+1, [Cur | Acc]). % For the "."!

%% @doc Little-Endian Base 128 (LEB128) Decoder
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

%% %% @doc In 64-bit the Address has size: 8 bytes (else 4).
%% %%      TODO: read from object file!
%% is64Bit() ->
%%   ?ELF_ADDR_SIZE =:= 8.
