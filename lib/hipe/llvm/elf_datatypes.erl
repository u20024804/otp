%% -*- erlang-indent-level: 2 -*-

%%% @copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%%                      Chris Stavrakakis <hydralisk.r@gmail.com>
%%% @author Yiannis Tsiouris <yiannis.tsiouris@gmail.com>
%%%    [http://www.softlab.ntua.gr/~gtsiour/]

%%%
%%% @doc Provides abstract datatypes and accessors for ELF structures.
%%%

-module(elf_datatypes).

-export([
	 %% File header
	 mk_ehdr/14,
	 ehdr_shoff/1,
	 ehdr_shentsize/1,
	 ehdr_shnum/1,
	 ehdr_shstrndx/1,
	 mk_ehdr_ident/7,
	 %% Section header table entries
	 mk_shdr/10,
	 shdr_offset/1,
	 shdr_size/1,
	 %% Symbol table entries
	 mk_sym/6,
	 sym_name/1,
	 sym_value/1,
	 sym_size/1,
	 %% Relocations
	 mk_rel/2,
	 mk_rela/3,
	 r_offset/1,
	 r_info/1,
	 rela_addend/1,
	 %% GCC exception table
	 mk_gccexntab_callsite/4,
	 gccexntab_callsite_start/1,
	 gccexntab_callsite_size/1,
	 gccexntab_callsite_lp/1
	]).

-export_type([elf_ehdr/0, elf_ehdr_ident/0, elf_rela/0, elf_gccexntab_callsite/0]).

%%------------------------------------------------------------------------------
%% Types
%%------------------------------------------------------------------------------

-type lp()     :: non_neg_integer().  % landing pad
-type num()    :: non_neg_integer().
-type index()  :: non_neg_integer().
-type offset() :: non_neg_integer().
-type size()   :: non_neg_integer().
-type start()  :: non_neg_integer().

-type info()     :: index().
-type nameoff()  :: offset().
-type valueoff() :: offset().

%%------------------------------------------------------------------------------
%% Abstract Data Types
%%------------------------------------------------------------------------------

%% File header
-record(elf_ehdr, {e_ident,     % ELF identification
		   e_type,      % Object file type
		   e_machine,   % Machine Type
		   e_version,   % Object file version
		   e_entry,     % Entry point address
		   e_phoff,     % Program header offset
		   e_shoff      :: offset(),     % Section header offset
		   e_flags,     % Processor-specific flags
		   e_ehsize     :: size(),    % ELF header size
		   e_phentsize, % Size of program header entry
		   e_phnum      :: num(),     % Number of program header entries
		   e_shentsize, % Size of section header entry
		   e_shnum      :: num(),     % Number of section header entries
		   e_shstrndx   :: index()    % Section name string table index
		  }).
-opaque elf_ehdr() :: #elf_ehdr{}.

-record(elf_ehdr_ident, {ei_class,      % File class
			 ei_data,       % Data encoding
			 ei_version,    % File version
			 ei_osabi,      % OS/ABI identification
			 ei_abiversion, % ABI version
			 ei_pad,        % Start of padding bytes
			 ei_nident      % Size of e_ident[]
			}).
-opaque elf_ehdr_ident() :: #elf_ehdr_ident{}.

%% Section header entries
-record(elf_shdr, {sh_name,      % Section name
		   sh_type,      % Section type
		   sh_flags,     % Section attributes
		   sh_addr,      % Virtual address in memory
		   sh_offset     :: offset(),    % Offset in file
		   sh_size       :: size(),      % Size of section
		   sh_link,      % Link to other section
		   sh_info,      % Miscellaneous information
		   sh_addralign, % Address align boundary
		   sh_entsize    % Size of entries, if section has table
		  }).
-type elf_shdr() :: #elf_shdr{}.

%% Symbol table entries
-record(elf_sym, {st_name   :: nameoff(),  % Symbol name
		  st_info,  % Type and Binding attributes
		  st_other, % Reserved
		  st_shndx, % Section table index
		  st_value  :: valueoff(), % Symbol value
		  st_size   :: size()      % Size of object
		 }).
-type elf_sym() :: #elf_sym{}.

%% Relocations
-record(elf_rel, {r_offset  :: offset(),  % Address of reference
		  r_info    :: info()     % Symbol index and type of relocation
		 }).
-type elf_rel() :: #elf_rel{}.

-record(elf_rela, {r_offset  :: offset(), % Address of reference
		   r_info    :: info(),   % Symbol index and type of relocation
		   r_addend  :: offset()  % Constant part of expression
		  }).
-type elf_rela() :: #elf_rela{}.

%% %% Program header table
%% -record(elf_phdr, {p_type,   % Type of segment
%% 		   p_flags,  % Segment attributes
%% 		   p_offset, % Offset in file
%% 		   p_vaddr,  % Virtual address in memory
%% 		   p_paddr,  % Reserved
%% 		   p_filesz, % Size of segment in file
%% 		   p_memsz,  % Size of segment in memory
%% 		   p_align   % Alignment of segment
%% 		  }).

%% %% GCC exception table
%% -record(elf_gccexntab, {ge_lpbenc,    % Landing pad base encoding
%% 			ge_lpbase,    % Landing pad base
%% 			ge_ttenc,     % Type table encoding
%% 			ge_ttoff,     % Type table offset
%% 			ge_csenc,     % Call-site table encoding
%% 			ge_cstabsize, % Call-site table size
%% 			ge_cstab     :: cstab() % Call-site table
%% 		       }).
%% -opaque elf_gccexntab() :: #elf_gccexntab{}.

-record(elf_gccexntab_callsite, {gee_start :: start(), % Call-site start
				 gee_size  :: size(),  % Call-site size
				 gee_lp    :: lp(),    % Call-site landing pad
						       % (exception handler)
				 gee_onaction % On action (e.g. cleanup)
				}).
-opaque elf_gccexntab_callsite() :: #elf_gccexntab_callsite{}.

%%------------------------------------------------------------------------------
%% Accessor Functions
%%------------------------------------------------------------------------------

%% File header
%% -spec mk_ehdr(...) -> elf_ehrd().
mk_ehdr(Ident, Type, Machine, Version, Entry, Phoff, Shoff, Flags, Ehsize,
	Phentsize, Phnum, Shentsize, Shnum, Shstrndx) ->
    #elf_ehdr{e_ident=Ident, e_type=Type, e_machine=Machine, e_version=Version,
	      e_entry=Entry, e_phoff=Phoff, e_shoff=Shoff, e_flags=Flags,
	      e_ehsize=Ehsize, e_phentsize=Phentsize, e_phnum=Phnum,
	      e_shentsize=Shentsize, e_shnum=Shnum, e_shstrndx=Shstrndx}.

-spec ehdr_shoff(elf_ehdr()) -> offset().
ehdr_shoff(#elf_ehdr{e_shoff=Offset}) -> Offset.

-spec ehdr_shentsize(elf_ehdr()) -> size().
ehdr_shentsize(#elf_ehdr{e_shentsize=Size}) -> Size.

-spec ehdr_shnum(elf_ehdr()) -> num().
ehdr_shnum(#elf_ehdr{e_shnum=Num}) -> Num.

-spec ehdr_shstrndx(elf_ehdr()) -> index().
ehdr_shstrndx(#elf_ehdr{e_shstrndx=Index}) -> Index.


%%-spec mk_ehdr_ident(...) -> elf_ehdr_ident().
mk_ehdr_ident(Class, Data, Version, OsABI, AbiVersion, Pad, Nident) ->
  #elf_ehdr_ident{ei_class=Class, ei_data=Data, ei_version=Version,
		  ei_osabi=OsABI, ei_abiversion=AbiVersion, ei_pad=Pad,
		  ei_nident=Nident}.

%%%-------------------------
%%% Section header entries
%%%-------------------------
mk_shdr(Name, Type, Flags, Addr, Offset, Size, Link, Info, AddrAlign, EntSize) ->
    #elf_shdr{sh_name=Name, sh_type=Type, sh_flags=Flags, sh_addr=Addr,
	      sh_offset=Offset, sh_size=Size, sh_link=Link, sh_info=Info,
	      sh_addralign=AddrAlign, sh_entsize=EntSize}.

-spec shdr_offset(elf_shdr()) -> offset().
shdr_offset(#elf_shdr{sh_offset=Offset}) -> Offset.

-spec shdr_size(elf_shdr()) -> size().
shdr_size(#elf_shdr{sh_size=Size}) -> Size.

%%%-------------------------
%%% Symbol Table Entries
%%%-------------------------
mk_sym(Name, Info, Other, Shndx, Value, Size) ->
  #elf_sym{st_name=Name, st_info=Info, st_other=Other,
	   st_shndx=Shndx, st_value=Value, st_size=Size}.

-spec sym_name(elf_sym()) -> nameoff().
sym_name(#elf_sym{st_name=Name}) -> Name.

-spec sym_value(elf_sym()) -> valueoff().
sym_value(#elf_sym{st_value=Value}) -> Value.

-spec sym_size(elf_sym()) -> size().
sym_size(#elf_sym{st_size=Size}) -> Size.

%%%-------------------------
%%% Relocations
%%%-------------------------
-spec mk_rel(offset(), info()) -> elf_rel().
mk_rel(Offset, Info) ->
  #elf_rel{r_offset=Offset, r_info=Info}.

%% The following two functions capitalize on the fact that the two kinds of
%% relocation records (for 32- and 64-bit architectures have similar structure.

-spec r_offset(elf_rel() | elf_rela()) -> offset().
r_offset(#elf_rel{r_offset=Offset}) -> Offset;
r_offset(#elf_rela{r_offset=Offset}) -> Offset.

-spec r_info(elf_rel() | elf_rela()) -> info().
r_info(#elf_rel{r_info=Info}) -> Info;
r_info(#elf_rela{r_info=Info}) -> Info.

-spec mk_rela(offset(), info(), offset()) -> elf_rela().
mk_rela(Offset, Info, Addend) ->
  #elf_rela{r_offset=Offset, r_info=Info, r_addend=Addend}.

-spec rela_addend(elf_rela()) -> offset().
rela_addend(#elf_rela{r_addend=Addend}) -> Addend.

%% %%%-------------------------
%% %%% GCC exception table
%% %%%-------------------------
%% -type cstab()  :: [elf_gccexntab_callsite()].
%%
%% mk_gccexntab(LPbenc, LPbase, TTenc, TToff, CSenc, CStabsize, CStab) ->
%%   #elf_gccexntab{ge_lpbenc=LPbenc, ge_lpbase=LPbase, ge_ttenc=TTenc,
%% 		 ge_ttoff=TToff, ge_csenc=CSenc, ge_cstabsize=CStabsize,
%% 		 ge_cstab=CStab}.
%%
%% -spec gccexntab_cstab(elf_gccexntab()) -> cstab().
%% gccexntab_cstab(#elf_gccexntab{ge_cstab=CSTab}) -> CSTab.

mk_gccexntab_callsite(Start, Size, LP, Action) ->
   #elf_gccexntab_callsite{gee_start=Start, gee_size=Size, gee_lp=LP,
			   gee_onaction=Action}.

-spec gccexntab_callsite_start(elf_gccexntab_callsite()) -> start().
gccexntab_callsite_start(#elf_gccexntab_callsite{gee_start=Start}) -> Start.

-spec gccexntab_callsite_size(elf_gccexntab_callsite()) -> size().
gccexntab_callsite_size(#elf_gccexntab_callsite{gee_size=Size}) -> Size.

-spec gccexntab_callsite_lp(elf_gccexntab_callsite()) -> lp().
gccexntab_callsite_lp(#elf_gccexntab_callsite{gee_lp=LP}) -> LP.
