%% -*- erlang-indent-level: 2 -*-

%%% @copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%%                      Chris Stavrakakis <hydralisk.r@gmail.com>
%%% @author Yiannis Tsiouris <yiannis.tsiouris@gmail.com>
%%%    [http://www.softlab.ntua.gr/~gtsiour/]

%%%
%%% @doc Provides accessors for ELF structs.
%%%

-module(elf_datatypes).

-export([
	 %% File header
	 mk_ehdr/14,
	 ehdr_field/2,
	 mk_ehdr_ident/7,
	 ehdr_ident_field/2,
	 %% Section header table entries
	 mk_shdr/10,
	 shdr_field/2,
	 %% Symbol table entries
	 mk_sym/6,
	 sym_field/2,
	 %% Relocations
	 mk_rel/2,
	 rel_field/2,
	 mk_rela/3,
	 rela_field/2,
	 %% GCC exception table
	 mk_gccexntab/7,
	 gccexntab_field/2,
	 mk_gccexntab_callsite/4,
	 gccexntab_callsite_field/2
	]).

-include("elf_datatypes.hrl").

%% File header
mk_ehdr(Ident, Type, Machine, Version, Entry, Phoff, Shoff, Flags, Ehsize,
	Phentsize, Phnum, Shentsize, Shnum, Shstrndx
	) ->
    #elf_ehdr{e_ident=Ident, e_type=Type, e_machine=Machine, e_version=Version,
	      e_entry=Entry, e_phoff=Phoff, e_shoff=Shoff, e_flags=Flags,
	      e_ehsize=Ehsize, e_phentsize=Phentsize, e_phnum=Phnum,
	      e_shentsize=Shentsize, e_shnum=Shnum, e_shstrndx=Shstrndx}.

ehdr_field(Ehdr, e_ident)     -> Ehdr#elf_ehdr.e_ident;
ehdr_field(Ehdr, e_type)      -> Ehdr#elf_ehdr.e_type;
ehdr_field(Ehdr, e_machine)   -> Ehdr#elf_ehdr.e_machine;
ehdr_field(Ehdr, e_version)   -> Ehdr#elf_ehdr.e_version;
ehdr_field(Ehdr, e_entry)     -> Ehdr#elf_ehdr.e_entry;
ehdr_field(Ehdr, e_phoff)     -> Ehdr#elf_ehdr.e_phoff;
ehdr_field(Ehdr, e_shoff)     -> Ehdr#elf_ehdr.e_shoff;
ehdr_field(Ehdr, e_flags)     -> Ehdr#elf_ehdr.e_flags;
ehdr_field(Ehdr, e_ehsize)    -> Ehdr#elf_ehdr.e_ehsize;
ehdr_field(Ehdr, e_phentsize) -> Ehdr#elf_ehdr.e_phentsize;
ehdr_field(Ehdr, e_phnum)     -> Ehdr#elf_ehdr.e_phnum;
ehdr_field(Ehdr, e_shentsize) -> Ehdr#elf_ehdr.e_shentsize;
ehdr_field(Ehdr, e_shnum)     -> Ehdr#elf_ehdr.e_shnum;
ehdr_field(Ehdr, e_shstrndx)  -> Ehdr#elf_ehdr.e_shstrndx.

mk_ehdr_ident(EI_Class, EI_Data, EI_Version, EI_Osabi, EI_Abiversion, EI_Pad,
	      EI_Nident) ->
  #elf_ehdr_ident{ei_class=EI_Class, ei_data=EI_Data, ei_version=EI_Version,
		  ei_osabi=EI_Osabi, ei_abiversion=EI_Abiversion, ei_pad=EI_Pad,
		  ei_nident=EI_Nident}.

ehdr_ident_field(Ident, ei_class)      -> Ident#elf_ehdr_ident.ei_class;
ehdr_ident_field(Ident, ei_data)       -> Ident#elf_ehdr_ident.ei_data;
ehdr_ident_field(Ident, ei_version)    -> Ident#elf_ehdr_ident.ei_version;
ehdr_ident_field(Ident, ei_osabi)      -> Ident#elf_ehdr_ident.ei_osabi;
ehdr_ident_field(Ident, ei_abiversion) -> Ident#elf_ehdr_ident.ei_abiversion;
ehdr_ident_field(Ident, ei_pad)        -> Ident#elf_ehdr_ident.ei_pad;
ehdr_ident_field(Ident, ei_nident)     -> Ident#elf_ehdr_ident.ei_nident.

%% Section header entries
mk_shdr(Name, Type, Flags, Addr, Offset, Size, Link, Info, Addralign, Entsize) ->
    #elf_shdr{sh_name=Name, sh_type=Type, sh_flags=Flags, sh_addr=Addr,
	      sh_offset=Offset, sh_size=Size, sh_link=Link, sh_info=Info,
	      sh_addralign=Addralign, sh_entsize=Entsize
	     }.

shdr_field(Shdr, sh_name)      -> Shdr#elf_shdr.sh_name;
shdr_field(Shdr, sh_type)      -> Shdr#elf_shdr.sh_type;
shdr_field(Shdr, sh_flags)     -> Shdr#elf_shdr.sh_flags;
shdr_field(Shdr, sh_addr)      -> Shdr#elf_shdr.sh_addr;
shdr_field(Shdr, sh_offset)    -> Shdr#elf_shdr.sh_offset;
shdr_field(Shdr, sh_size)      -> Shdr#elf_shdr.sh_size;
shdr_field(Shdr, sh_link)      -> Shdr#elf_shdr.sh_link;
shdr_field(Shdr, sh_info)      -> Shdr#elf_shdr.sh_info;
shdr_field(Shdr, sh_addralign) -> Shdr#elf_shdr.sh_addralign;
shdr_field(Shdr, sh_entsize)   -> Shdr#elf_shdr.sh_entsize.

%% Symbol Table
mk_sym(Name, Info, Other, Shndx, Value, Size) ->
    #elf_sym{st_name=Name, st_info=Info, st_other=Other,
	     st_shndx=Shndx, st_value=Value, st_size=Size
	    }.
sym_field(Sym, st_name)  -> Sym#elf_sym.st_name;
sym_field(Sym, st_info)  -> Sym#elf_sym.st_info;
sym_field(Sym, st_other) -> Sym#elf_sym.st_other;
sym_field(Sym, st_shndx) -> Sym#elf_sym.st_shndx;
sym_field(Sym, st_value) -> Sym#elf_sym.st_value;
sym_field(Sym, st_size)  -> Sym#elf_sym.st_size.

%% Relocations
mk_rel(Offset, Info) ->
    #elf_rel{r_offset=Offset, r_info=Info}.
rel_field(Rel, r_offset) -> Rel#elf_rel.r_offset;
rel_field(Rel, r_info)   -> Rel#elf_rel.r_info.

mk_rela(Offset, Info, Addend) ->
    #elf_rela{r_offset=Offset, r_info=Info, r_addend=Addend}.
rela_field(Rela, r_offset) -> Rela#elf_rela.r_offset;
rela_field(Rela, r_info)   -> Rela#elf_rela.r_info;
rela_field(Rela, r_addend) -> Rela#elf_rela.r_addend.

%% GCC exception table
mk_gccexntab(LPbenc, LPbase, TTenc, TToff, CSenc, CStabsize, CStab) ->
  #elf_gccexntab{ge_lpbenc=LPbenc, ge_lpbase=LPbase, ge_ttenc=TTenc,
		 ge_ttoff=TToff, ge_csenc=CSenc, ge_cstabsize=CStabsize,
		 ge_cstab=CStab}.
gccexntab_field(Ge, ge_lpbenc)    -> Ge#elf_gccexntab.ge_lpbenc;
gccexntab_field(Ge, ge_lpbase)    -> Ge#elf_gccexntab.ge_lpbase;
gccexntab_field(Ge, ge_ttenc)     -> Ge#elf_gccexntab.ge_ttenc;
gccexntab_field(Ge, ge_ttoff)     -> Ge#elf_gccexntab.ge_ttoff;
gccexntab_field(Ge, ge_csenc)     -> Ge#elf_gccexntab.ge_csenc;
gccexntab_field(Ge, ge_cstabsize) -> Ge#elf_gccexntab.ge_cstabsize;
gccexntab_field(Ge, ge_cstab)     -> Ge#elf_gccexntab.ge_cstab.

mk_gccexntab_callsite(Start, Size, LP, Action) ->
   #elf_gccexntab_callsite{gee_start=Start, gee_size=Size, gee_lp=LP,
			   gee_onaction=Action}.
gccexntab_callsite_field(CsE, gee_start)    ->
  CsE#elf_gccexntab_callsite.gee_start;
gccexntab_callsite_field(CsE, gee_size)     ->
  CsE#elf_gccexntab_callsite.gee_size;
gccexntab_callsite_field(CsE, gee_lp)       ->
  CsE#elf_gccexntab_callsite.gee_lp;
gccexntab_callsite_field(CsE, gee_onaction) ->
  CsE#elf_gccexntab_callsite.gee_onaction.
