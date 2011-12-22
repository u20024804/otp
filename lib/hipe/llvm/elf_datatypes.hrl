%% -*- erlang-indent-level: 2 -*-

%%% @copyright 2011-2012 Yiannis Tsiouris <yiannis.tsiouris@gmail.com>,
%%%                      Chris Stavrakakis <hydralisk.r@gmail.com>
%%% @author Yiannis Tsiouris <yiannis.tsiouris@gmail.com>
%%%    [http://www.softlab.ntua.gr/~gtsiour/]

%%%
%%% @doc Provides abstract datatypes for various ELF struct.
%%%

%% File header
-record(elf_ehdr, {e_ident,     % ELF identification
		   e_type,      % Object file type
		   e_machine,   % Machine Type
		   e_version,   % Object file version
		   e_entry,     % Entry point address
		   e_phoff,     % Program header offset
		   e_shoff,     % Section header offset
		   e_flags,     % Processor-specific flags
		   e_ehsize,    % ELF header size
		   e_phentsize, % Size of program header entry
		   e_phnum,     % Number of program header entries
		   e_shentsize, % Size of section header entry
		   e_shnum,     % Number of section header entries
		   e_shstrndx   % Section name string table index
		  }).
-record(elf_ehdr_ident, {ei_class,      % File class
			 ei_data,       % Data encoding
			 ei_version,    % File version
			 ei_osabi,      % OS/ABI identification
			 ei_abiversion, % ABI version
			 ei_pad,        % Start of padding bytes
			 ei_nident      % Size of e_ident[]
			}).
%% Section header entries
-record(elf_shdr, {sh_name,      % Section name
		   sh_type,      % Section type
		   sh_flags,     % Section attributes
		   sh_addr,      % Virtual address in memory
		   sh_offset,    % Offset in file
		   sh_size,      % Size of section
		   sh_link,      % Link to other section
		   sh_info,      % Miscellaneous information
		   sh_addralign, % Address align boundary
		   sh_entsize    % Size of entries, if section has table
		  }).
%% Symbol table
-record(elf_sym, {st_name,  % Symbol name
		  st_info,  % Type and Binding attributes
		  st_other, % Reserved
		  st_shndx, % Section table index
		  st_value, % Symbol value
		  st_size   % Size of object
		 }).
%% Relocations
-record(elf_rel, {r_offset, % Address of reference
		  r_info   % Symbol index and type of relocation
		 }).
-record(elf_rela, {r_offset, % Address of reference
		   r_info,   % Symbol index and type of relocation
		   r_addend  % Constant part of expression
		  }).
%% Program header table
-record(elf_phdr, {p_type,   % Type of segment
		   p_flags,  % Segment attributes
		   p_offset, % Offset in file
		   p_vaddr,  % Virtual address in memory
		   p_paddr,  % Reserved
		   p_filesz, % Size of segment in file
		   p_memsz,  % Size of segment in memory
		   p_align   % Alignment of segment
		  }).
%% GCC exception table
-record(elf_gccexntab, {ge_lpbenc,    % Landing pad base encoding
			ge_lpbase,    % Landing pad base
			ge_ttenc,     % Type table encoding
			ge_ttoff,     % Type table offset
			ge_csenc,     % Call-site table encoding
			ge_cstabsize, % Call-site table size
			ge_cstab      % Call-site table
		       }).
-record(elf_gccexntab_callsite, {gee_start,   % Call-site start
				 gee_size,    % Call-site size
				 gee_lp,      % Call-site landing pad (exception
						%   handler)
				 gee_onaction % On action (e.g. cleanup)
				}).
