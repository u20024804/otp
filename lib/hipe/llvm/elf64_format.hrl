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

%%% @doc This header file contains very very useful macros for manipulating
%%%      various segments of an ELF-64 formated object file, such as sizes,
%%%      offsets and predefined constants. For further information about 
%%%      each field take a quick look at 
%%%      "[http://www.linuxjournal.com/article/1060?page=0,0]" that contains
%%%      the current HP/Intel definition of the ELF-64 object file format.

%%------------------------------------------------------------------------------
%% 
%%                        Elf64_format Header File
%%
%%------------------------------------------------------------------------------


%%------------------------------------------------------------------------------
%% ELF-64 Data Types (in bytes)
%%------------------------------------------------------------------------------
-define(ELF64_ADDR_SIZE,          8).
-define(ELF64_OFF_SIZE,           8).
-define(ELF64_HALF_SIZE,          2).
-define(ELF64_WORD_SIZE,          4).
-define(ELF64_SWORD_SIZE,         4).
-define(ELF64_XWORD_SIZE,         8).
-define(ELF64_SXWORD_SIZE,        8).
-define(ELF64_UNSIGNED_CHAR_SIZE, 1).


%%------------------------------------------------------------------------------
%% ELF-64 File Header
%%------------------------------------------------------------------------------
-define(ELF64_EHDR_SIZE, (?E_IDENT_SIZE + ?E_TYPE_SIZE + ?E_MACHINE_SIZE
			 +?E_VERSION_SIZE + ?E_ENTRY_SIZE + ?E_PHOFF_SIZE
			 +?E_SHOFF_SIZE + ?E_FLAGS_SIZE + ?E_EHSIZE_SIZE
			 +?E_PHENTSIZE_SIZE + ?E_PHNUM_SIZE + ?E_SHENTSIZE_SIZE 
			 +?E_SHNUM_SIZE + ?E_SHSTRNDX_SIZE) 
       ). % 64 bytes

-define(E_IDENT_SIZE,     (16 * ?ELF64_UNSIGNED_CHAR_SIZE) ). % 16 bytes
-define(E_TYPE_SIZE,      ?ELF64_HALF_SIZE).                  % 2 bytes
-define(E_MACHINE_SIZE,   ?ELF64_HALF_SIZE).                  % 2 bytes
-define(E_VERSION_SIZE,   ?ELF64_WORD_SIZE).                  % 4 bytes
-define(E_ENTRY_SIZE,     ?ELF64_ADDR_SIZE).                  % 8 bytes
-define(E_PHOFF_SIZE,     ?ELF64_OFF_SIZE).                   % 8 bytes
-define(E_SHOFF_SIZE,     ?ELF64_OFF_SIZE).                   % 8 bytes
-define(E_FLAGS_SIZE,     ?ELF64_WORD_SIZE).                  % 4 bytes
-define(E_EHSIZE_SIZE,    ?ELF64_HALF_SIZE).                  % 2 bytes
-define(E_PHENTSIZE_SIZE, ?ELF64_HALF_SIZE).                  % 2 bytes
-define(E_PHNUM_SIZE,     ?ELF64_HALF_SIZE).                  % 2 bytes
-define(E_SHENTSIZE_SIZE, ?ELF64_HALF_SIZE).                  % 2 bytes
-define(E_SHNUM_SIZE,     ?ELF64_HALF_SIZE).                  % 2 bytes
-define(E_SHSTRNDX_SIZE,  ?ELF64_HALF_SIZE).                  % 2 bytes

%% Useful arithmetics for computing byte offsets for various File Header 
%% entries from a File Header (erlang) binary
-define(E_IDENT_OFFSET,     0).                                          % 0 bytes
-define(E_TYPE_OFFSET,      (?E_IDENT_OFFSET + ?E_IDENT_SIZE) ).         % 16 bytes
-define(E_MACHINE_OFFSET,   (?E_TYPE_OFFSET + ?E_TYPE_SIZE) ).           % 18 bytes
-define(E_VERSION_OFFSET,   (?E_MACHINE_OFFSET + ?E_MACHINE_SIZE) ).     % 20 bytes
-define(E_ENTRY_OFFSET,     (?E_VERSION_OFFSET + ?E_VERSION_SIZE) ).     % 24 bytes
-define(E_PHOFF_OFFSET,     (?E_ENTRY_OFFSET + ?E_ENTRY_SIZE) ).         % 32 bytes
-define(E_SHOFF_OFFSET,     (?E_PHOFF_OFFSET + ?E_PHOFF_SIZE) ).         % 40 bytes
-define(E_FLAGS_OFFSET,     (?E_SHOFF_OFFSET + ?E_SHOFF_SIZE) ).         % 48 bytes
-define(E_EHSIZE_OFFSET,    (?E_FLAGS_OFFSET + ?E_FLAGS_SIZE) ).         % 52 bytes
-define(E_PHENTSIZE_OFFSET, (?E_EHSIZE_OFFSET + ?E_EHSIZE_SIZE) ).       % 54 bytes
-define(E_PHNUM_OFFSET,     (?E_PHENTSIZE_OFFSET + ?E_PHENTSIZE_SIZE) ). % 56 bytes
-define(E_SHENTSIZE_OFFSET, (?E_PHNUM_OFFSET + ?E_PHNUM_SIZE) ).         % 58 bytes
-define(E_SHNUM_OFFSET,     (?E_SHENTSIZE_OFFSET + ?E_SHENTSIZE_SIZE) ). % 60 bytes
-define(E_SHSTRNDX_OFFSET,  (?E_SHNUM_OFFSET + ?E_SHNUM_SIZE) ).         % 62 bytes

%% Name aliases of File Header fields information used in get_header_field 
%% function of elf64_format module.
-define(E_IDENT,     {?E_IDENT_OFFSET, ?E_IDENT_SIZE}).
-define(E_TYPE,      {?E_TYPE_OFFSET, ?E_TYPE_SIZE}).
-define(E_MACHINE,   {?E_MACHINE_OFFSET, ?E_MACHINE_SIZE}).
-define(E_VERSION,   {?E_VERSION_OFFSET, ?E_VERSION_SIZE})
-define(E_ENTRY,     {?E_ENTRY_OFFSET, ?E_ENTRY_SIZE}).
-define(E_PHOFF,     {?E_PHOFF_OFFSET, ?E_PHOFF_SIZE}).
-define(E_SHOFF,     {?E_SHOFF_OFFSET, ?E_SHOFF_SIZE}).
-define(E_FLAGS,     {?E_FLAGS_OFFSET, ?E_FLAGS_SIZE}).
-define(E_EHSIZE,    {?E_EHSIZE_OFFSET, ?E_EHSIZE_SIZE}).
-define(E_PHENTSIZE, {?E_PHENTSIZE_OFFSET, ?E_PHENTSIZE_SIZE}).
-define(E_PHNUM,     {?E_PHNUM_OFFSET, ?E_PHNUM_SIZE}).
-define(E_SHENTSIZE, {?E_SHENTSIZE_OFFSET, ?E_SHENTSIZE_SIZE}).
-define(E_SHNUM,     {?E_SHNUM_OFFSET, ?E_SHNUM_SIZE}).
-define(E_SHSTRNDX,  {?E_SHSTRNDX_OFFSET, ?E_SHSTRNDX_SIZE}).

%% ELF Identification (e_ident)
-define(EI_MAG0,       0).
-define(EI_MAG1,       1).
-define(EI_MAG2,       2).
-define(EI_MAG3,       3).
-define(EI_CLASS,      4).
-define(EI_DATA,       5).
-define(EI_VERSION,    6).
-define(EI_OSABI,      7).
-define(EI_ABIVERSION, 8).
-define(EI_PAD,        9).
-define(EI_NIDENT,     16).

%% Object File Classes (e_ident[EI_CLASS])
-define(ELFCLASS32, 1).
-define(ELFCLASS64, 2).

%% Data Encodings (e_ident[EI_DATA])
-define(ELFDATA2LSB, 1).
-define(ELFDATA2MSB, 2).

%% Operating System and ABI Identifiers (e_ident[EI_OSABI])
-define(ELFOSABI_SYSV,       0).
-define(ELFOSABI_HPUX,       1).
-define(ELFOSABI_STANDALONE, 255).

%% Object File Types (e_type)
-define(ET_NONE,   0).
-define(ET_REL,    1).
-define(ET_EXEC,   2).
-define(ET_DYN,    3).
-define(ET_CORE,   4).
-define(ET_LOOS,   16#FE00).
-define(ET_HIOS,   16#FEFF).
-define(ET_LOPROC, 16#FF00).
-define(ET_HIPROC, 16#FFFF).


%%------------------------------------------------------------------------------
%% ELF-64 Section Header
%%------------------------------------------------------------------------------
-define(ELF64_SHDRENTRY_SIZE, (?SH_NAME_SIZE + ?SH_TYPE_SIZE + ?SH_FLAGS_SIZE
			      +?SH_ADDR_SIZE + ?SH_OFFSET_SIZE + ?SH_SIZE_SIZE
			      +?SH_LINK_SIZE + ?SH_INFO_SIZE 
			      +?SH_ADDRALIGN_SIZE + ?SH_ENTSIZE_SIZE) 
       ). % 64 bytes 

-define(SH_NAME_SIZE,      ?ELF64_WORD_SIZE).  % 4 bytes
-define(SH_TYPE_SIZE,      ?ELF64_WORD_SIZE).  % 4 bytes
-define(SH_FLAGS_SIZE,     ?ELF64_XWORD_SIZE). % 8 bytes
-define(SH_ADDR_SIZE,      ?ELF64_ADDR_SIZE).  % 8 bytes
-define(SH_OFFSET_SIZE,    ?ELF64_OFF_SIZE).   % 8 bytes
-define(SH_SIZE_SIZE,      ?ELF64_XWORD_SIZE). % 8 bytes
-define(SH_LINK_SIZE,      ?ELF64_WORD_SIZE).  % 4 bytes
-define(SH_INFO_SIZE,      ?ELF64_WORD_SIZE).  % 4 bytes
-define(SH_ADDRALIGN_SIZE, ?ELF64_XWORD_SIZE). % 8 bytes
-define(SH_ENTSIZE_SIZE,   ?ELF64_XWORD_SIZE). % 8 bytes

%% Useful arithmetics for computing byte offsets for various fields from a 
%% Section Header Entry (erlang) binary
-define(SH_NAME_OFFSET,      0).                                           % 0 bytes
-define(SH_TYPE_OFFSET,      (?SH_NAME_OFFSET + ?SH_NAME_SIZE) ).          % 4 bytes
-define(SH_FLAGS_OFFSET,     (?SH_TYPE_OFFSET + ?SH_TYPE_SIZE) ).          % 8 bytes
-define(SH_ADDR_OFFSET,      (?SH_FLAGS_OFFSET + ?SH_FLAGS_SIZE) ).        % 16 bytes
-define(SH_OFFSET_OFFSET,    (?SH_ADDR_OFFSET + ?SH_ADDR_SIZE) ).          % 24 bytes
-define(SH_SIZE_OFFSET,      (?SH_OFFSET_OFFSET + ?SH_OFFSET_SIZE) ).      % 32 bytes
-define(SH_LINK_OFFSET,      (?SH_SIZE_OFFSET + ?SH_SIZE_SIZE) ).          % 40 bytes
-define(SH_INFO_OFFSET,      (?SH_LINK_OFFSET + ?SH_LINK_SIZE) ).          % 44 bytes
-define(SH_ADDRALIGN_OFFSET, (?SH_INFO_OFFSET + ?SH_INFO_SIZE) ).          % 48 bytes
-define(SH_ENTSIZE_OFFSET,   (?SH_ADDRALIGN_OFFSET + ?SH_ADDRALIGN_SIZE) ).% 56 bytes

%% Name aliases of Section Header Table entry information used in 
%% get_shdrtab_entry function of elf64_format module. 
-define(SH_NAME,      {?SH_NAME_OFFSET, ?SH_NAME_SIZE}).
-define(SH_TYPE,      {?SH_TYPE_OFFSET, ?SH_TYPE_SIZE}).
-define(SH_FLAGS,     {?SH_FLAGS_OFFSET, ?SH_FLAGS_SIZE}).
-define(SH_ADDR,      {?SH_ADDR_OFFSET, ?SH_ADDR_SIZE}).
-define(SH_OFFSET,    {?SH_OFFSET_OFFSET, ?SH_OFFSET_SIZE}).
-define(SH_SIZE,      {?SH_SIZE_OFFSET, ?SH_SIZE_SIZE}).
-define(SH_LINK,      {?SH_LINK_OFFSET, ?SH_LINK_SIZE}).
-define(SH_INFO,      {?SH_INFO_OFFSET, ?SH_INFO_SIZE}).
-define(SH_ADDRALIGN, {?SH_ADDRALIGN_OFFSET, ?SH_ADDRALIGN_SIZE}).
-define(SH_ENTSIZE,   {?SH_ENTSIZE_OFFSET, ?SH_ENTSIZE_SIZE}).

%% Section Types (sh_type)
-define(SHT_NULL,     0).
-define(SHT_PROGBITS, 1).
-define(SHT_SYMTAB,   2).
-define(SHT_STRTAB,   3).
-define(SHT_RELA,     4).
-define(SHT_HASH,     5).
-define(SHT_DYNAMIC,  6).
-define(SHT_NOTE,     7).
-define(SHT_NOBITS,   8).
-define(SHT_REL,      9).
-define(SHT_SHLIB,    10).
-define(SHT_DYNSYM,   11).
-define(SHT_LOOS,     16#60000000).
-define(SHT_HIOS,     16#6FFFFFFF).
-define(SHT_LOPROC,   16#70000000).
-define(SHT_HIPROC,   16#7FFFFFFF).

%% Section Attributes (sh_flags)
-define(SHF_WRITE,     16#1).
-define(SHF_ALLOC,     16#2).
-define(SHF_EXECINSTR, 16#4).
-define(SHF_MASKOS,    16#0F000000).
-define(SHF_MASKPROC,  16#F0000000).

%%
%% Standar Section names for Code and Data
%%
-define(BSS,        ".bss").
-define(DATA,       ".data").
-define(INTERP,     ".interp").
-define(RODATA,     ".rodata").
-define(TEXT,       ".text").
%% Other Standar Section names
-define(COMMENT,    ".comment").
-define(DYNAMIC,    ".dynamic").
-define(DYNSTR,     ".dynstr").
-define(GOT,        ".got").
-define(HASH,       ".hash").
-define(NOTE(Name), (".note." ++ Name)).
-define(PLT,        ".plt").
-define(REL(Name),  (".rel" ++ Name) ).
-define(RELA(Name), (".rela" ++ Name) ).
-define(SHSTRTAB,   ".shstrtab").
-define(STRTAB,     ".strtab").
-define(SYMTAB,     ".symtab").
-define(GCC_EXN_TAB, ".gcc_except_table").


%%------------------------------------------------------------------------------
%% ELF-64 Symbol Table Entries
%%------------------------------------------------------------------------------
-define(ELF64_SYM_SIZE, (?ST_NAME_SIZE + ?ST_INFO_SIZE + ?ST_OTHER_SIZE
			+?ST_SHNDX_SIZE + ?ST_VALUE_SIZE + ?ST_SIZE_SIZE) 
       ). % 24 bytes

-define(ST_NAME_SIZE,  ?ELF64_WORD_SIZE).          % 4 bytes
-define(ST_INFO_SIZE,  ?ELF64_UNSIGNED_CHAR_SIZE). % 1 byte
-define(ST_OTHER_SIZE, ?ELF64_UNSIGNED_CHAR_SIZE). % 1 byte
-define(ST_SHNDX_SIZE, ?ELF64_HALF_SIZE).          % 2 bytes
-define(ST_VALUE_SIZE, ?ELF64_ADDR_SIZE).          % 8 bytes
-define(ST_SIZE_SIZE,  ?ELF64_XWORD_SIZE).         % 8 bytes

%% Precomputed offset for Symbol Table entries in SymTab binary
-define(ST_NAME_OFFSET,  0).                                    % 0 bytes
-define(ST_INFO_OFFSET,  (?ST_NAME_OFFSET + ?ST_NAME_SIZE) ).   % 4 bytes
-define(ST_OTHER_OFFSET, (?ST_INFO_OFFSET + ?ST_INFO_SIZE) ).   % 5 bytes
-define(ST_SHNDX_OFFSET, (?ST_OTHER_OFFSET + ?ST_OTHER_SIZE) ). % 6 bytes
-define(ST_VALUE_OFFSET, (?ST_SHNDX_OFFSET + ?ST_SHNDX_SIZE) ). % 8 bytes
-define(ST_SIZE_OFFSET,  (?ST_VALUE_OFFSET + ?ST_VALUE_SIZE) ). % 16 bytes

%% Name aliases for Symbol Table entry information
-define(ST_NAME,  {?ST_NAME_OFFSET, ?ST_NAME_SIZE}).
-define(ST_INFO,  {?ST_INFO_OFFSET, ?ST_INFO_SIZE}).
-define(ST_OTHER, {?ST_OTHER_OFFSET, ?ST_OTHER_SIZE}).
-define(ST_SHNDX, {?ST_SHNDX_OFFSET, ?ST_SHNDX_SIZE}).
-define(ST_VALUE, {?ST_VALUE_OFFSET, ?ST_VALUE_SIZE}).
-define(ST_SIZE,  {?ST_SIZE_OFFSET, ?ST_SIZE_SIZE}).

%% Symbol Bindings
-define(STB_LOCAL,  0).
-define(STB_GLOBAL, 1).
-define(STB_WEAK,   2).
-define(STB_LOOS,   10).
-define(STB_HIOS,   12).
-define(STB_LOPROC, 13).
-define(STB_HIPROC, 15).

%% Symbol Types
-define(STT_NOTYPE,  0).
-define(STT_OBJECT,  1).
-define(STT_FUNC,    2).
-define(STT_SECTION, 3).
-define(STT_FILE,    4).
-define(STT_LOOS,    10).
-define(STT_HIOS,    12).
-define(STT_LOPROC,  13).
-define(STT_HIPROC,  15).


%%------------------------------------------------------------------------------
%% ELF-64 Relocation Entries
%%------------------------------------------------------------------------------
-define(ELF64_REL_SIZE,  (?R_OFFSET_SIZE + ?R_INFO_SIZE) ).  % 16 bytes 
-define(ELF64_RELA_SIZE, (?R_OFFSET_SIZE + ?R_INFO_SIZE + ?R_ADDEND_SIZE) 
       ). % 24 bytes 

-define(R_OFFSET_SIZE, ?ELF64_ADDR_SIZE).   % 8 bytes
-define(R_INFO_SIZE,   ?ELF64_XWORD_SIZE).  % 8 bytes
-define(R_ADDEND_SIZE, ?ELF64_SXWORD_SIZE). % 8 bytes

%% Arithmetics for computing byte offsets in a Relocation entry binary
-define(R_OFFSET_OFFSET, 0).                                    % 0 bytes
-define(R_INFO_OFFSET,   (?R_OFFSET_OFFSET + ?R_OFFSET_SIZE) ). % 8 bytes
-define(R_ADDEND_OFFSET, (?R_INFO_OFFSET + ?R_INFO_SIZE) ).     % 16 bytes

%% Name aliases for Relocation field information
-define(R_OFFSET, {?R_OFFSET_OFFSET, ?R_OFFSET_SIZE}).
-define(R_INFO,   {?R_INFO_OFFSET, ?R_INFO_SIZE}).
-define(R_ADDEND, {?R_ADDEND_OFFSET, ?R_ADDEND_SIZE}).

%% Useful macros to extract information from r_info field
-define(ELF64_R_SYM(I),     (I bsr 32) ).
-define(ELF64_R_TYPE(I),    (I band 16#ffffffff) ).
-define(ELF64_R_INFO(S, T), ((S bsl 32) + (T band 16#ffffffff)) ).


%%------------------------------------------------------------------------------
%% ELF-64 Program Header Table
%%------------------------------------------------------------------------------
-define(ELF64_PHDR_SIZE, (?P_TYPE_SIZE + ?P_FLAGS_SIZE + ?P_OFFSET_SIZE
			 +?P_VADDR_SIZE + ?P_PADDR_SIZE + ?P_FILESZ_SIZE
			 +?P_MEMSZ_SIZE + ?P_ALIGN_SIZE)
       ). % 56 bytes 

-define(P_TYPE_SIZE,   ?ELF64_WORD_SIZE).  % 4 bytes
-define(P_FLAGS_SIZE,  ?ELF64_WORD_SIZE).  % 4 bytes
-define(P_OFFSET_SIZE, ?ELF64_OFF_SIZE).   % 8 bytes
-define(P_VADDR_SIZE,  ?ELF64_ADDR_SIZE).  % 8 bytes
-define(P_PADDR_SIZE,  ?ELF64_ADDR_SIZE).  % 8 bytes
-define(P_FILESZ_SIZE, ?ELF64_XWORD_SIZE). % 8 bytes
-define(P_MEMSZ_SIZE,  ?ELF64_XWORD_SIZE). % 8 bytes
-define(P_ALIGN_SIZE,  ?ELF64_XWORD_SIZE). % 8 bytes

%% Offsets of various fields in a Program Header Table entry binary.
-define(P_TYPE_OFFSET,   0).                                    % 0 bytes
-define(P_FLAGS_OFFSET,  (?P_TYPE_OFFSET + ?P_TYPE_SIZE) ).     % 4 bytes
-define(P_OFFSET_OFFSET, (?P_FLAGS_OFFSET + ?P_FLAGS_SIZE) ).   % 8 bytes
-define(P_VADDR_OFFSET,  (?P_OFFSET_OFFSET + ?P_OFFSET_SIZE) ). % 16 bytes
-define(P_PADDR_OFFSET,  (?P_VADDR_OFFSET + ?P_VADDR_SIZE) ).   % 24 bytes
-define(P_FILESZ_OFFSET, (?P_PVADDR_OFFSET + ?P_PVADDR_SIZE) ). % 32 bytes
-define(P_MEMSZ_OFFSET,  (?P_FILESZ_OFFSET + ?P_FILESZ_SIZE) ). % 40 bytes
-define(P_ALIGN_OFFSET,  (?P_MEMSZ_OFFSET + ?P_MEMSZ_SIZE) ).   % 48 bytes

%% Name aliases for each Program Header Table entry field information.
-define(P_TYPE,   {?P_TYPE_OFFSET, ?P_TYPE_SIZE} ).
-define(P_FLAGS,  {?P_FLAGS_OFFSET, ?P_FLAGS_SIZE} ).
-define(P_OFFSET, {?P_OFFSET_OFFSET, ?P_OFFSET_SIZE} ).
-define(P_VADDR,  {?P_VADDR_OFFSET, ?P_VADDR_SIZE} ).
-define(P_PADDR,  {?P_PADDR_OFFSET, ?P_PADDR_SIZE} ).
-define(P_FILESZ, {?P_FILESZ_OFFSET, ?P_FILESZ_SIZE} ).
-define(P_MEMSZ,  {?P_MEMSZ_OFFSET, ?P_MEMSZ_SIZE} ).
-define(P_ALIGN,  {?P_ALIGN_OFFSET, ?P_ALIGN_SIZE} ).

%% Segment Types (p_type)
-define(PT_NULL,    0).
-define(PT_LOAD,    1).
-define(PT_DYNAMIC, 2).
-define(PT_INTERP,  3).
-define(PT_NOTE,    4).
-define(PT_SHLIB,   5).
-define(PT_PHDR,    6).
-define(PT_LOOS,    16#60000000).
-define(PT_HIOS,    16#6FFFFFFF).
-define(PT_LOPROC,  16#70000000).
-define(PT_HIPROC,  16#7FFFFFFF).

%% Segment Attributes (p_flags)
-define(PF_X,        16#1).
-define(PF_W,        16#2).
-define(PF_R,        16#4).
-define(PF_MASKOS,   16#00FF0000).
-define(PF_MASKPROC, 16#FF000000).


%%------------------------------------------------------------------------------
%% ELF-64 Dynamic Table
%%------------------------------------------------------------------------------
-define(ELF64_DYN_SIZE, (?D_TAG_SIZE + ?D_VAL_PTR_SIZE) ). % 16 bytes 

-define(D_TAG_SIZE, ?ELF64_SXWORD_SIZE).   % 8 bytes
-define(D_VAL_PTR_SIZE, ?ELF64_ADDR_SIZE). % 8 bytes

%% Offsets of each field in Dynamic Table entry in binary
-define(D_TAG_OFFSET,     0).                             % 0 bytes
-define(D_VAL_PTR_OFFSET, (?D_TAG_OFFSET + ?D_TAG_SIZE)). % 8 bytes 

%% Name aliases for each field of a Dynamic Table entry information
-define(D_TAG,     {?D_TAG_OFFSET, ?D_TAG_SIZE} ).
-define(D_VAL_PTR, {?D_VAL_PTR_OFFSET, ?D_VAL_PTR_SIZE} ).

%% Dynamic Table Entries
-define(DT_NULL,         0).
-define(DT_NEEDED,       1).
-define(DT_PLTRELSZ,     2).
-define(DT_PLTGOT,       3).
-define(DT_HASH,         4).
-define(DT_STRTAB,       5).
-define(DT_SYMTAB,       6).
-define(DT_RELA,         7).
-define(DT_RELASZ,       8).
-define(DT_RELAENT,      9).
-define(DT_STRSZ,        10).
-define(DT_SYMENT,       11).
-define(DT_INIT,         12).
-define(DT_FINI,         13).
-define(DT_SONAME,       14).
-define(DT_RPATH,        15).
-define(DT_SYMBOLIC,     16).
-define(DT_REL,          17).
-define(DT_RELSZ,        18).
-define(DT_RELENT,       19).
-define(DT_PLTREL,       20).
-define(DT_DEBUG,        21).
-define(DT_TEXTREL,      22).
-define(DT_JMPREL,       23).
-define(DT_BIND_NOW,     24).
-define(DT_INIT_ARRAY,   25).
-define(DT_FINI_ARRAY,   26).
-define(DT_INIT_ARRAYSZ, 27).
-define(DT_FINI_ARRAYSZ, 28).
-define(DT_LOOS,         16#60000000).
-define(DT_HIOS,         16#6FFFFFFF).
-define(DT_LOPROC,       16#700000000).
-define(DT_HIPROC,       16#7FFFFFFFF).


%%------------------------------------------------------------------------------
%% ELF-64 GCC Exception Table 
%%------------------------------------------------------------------------------

%% The DWARF Exception Header Encoding is used to describe the type of data used
%% in the .eh_frame_hdr (and .gcc_except_table) section. The upper 4 bits 
%% indicate how the value is to be applied. The lower 4 bits indicate the format
%% of the data.

%% DWARF Exception Header value format
-define(DW_EH_PE_omit,    16#ff). % No value is present.
-define(DW_EH_PE_uleb128, 16#01). % Unsigned value encoded using LEB128.
-define(DW_EH_PE_udata2,  16#02). % A 2 bytes unsigned value.
-define(DW_EH_PE_udata4,  16#03). % A 4 bytes unsigned value.
-define(DW_EH_PE_udata8,  16#04). % An 8 bytes unsigned value.
-define(DW_EH_PE_sleb128, 16#09). % Signed value encoded using LEB128.
-define(DW_EH_PE_sdata2,  16#0a). % A 2 bytes signed value.
-define(DW_EH_PE_sdata4,  16#0b). % A 4 bytes signed value.
-define(DW_EH_PE_sdata8,  16#0c). % An 8 bytes signed value.

%% DWARF Exception Header application
-define(DW_EH_PE_absptr,  16#00). % Value is used with no modification.
-define(DW_EH_PE_pcrel,   16#10). % Value is relative to the current PC.
-define(DW_EH_PE_datarel, 16#30). % Value is relative to the beginning of the 
                                  %   section.


%%------------------------------------------------------------------------------
%% ELF-64 Read-only data (constants, literlas etc.)
%%------------------------------------------------------------------------------

-define(RO_ENTRY_SIZE, 8). % 8 bytes

%%------------------------------------------------------------------------------
%% Misc.
%%------------------------------------------------------------------------------
-define(bits(Bytes), (Bytes * 8)).

