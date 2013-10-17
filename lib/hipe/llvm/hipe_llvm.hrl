%% -*- erlang-indent-level: 2 -*-

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Abstract Data Types for LLVM Assembly.
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%% Terminator Instructions
-record(llvm_ret, {ret_list=[]}).
-type llvm_ret() :: #llvm_ret{}.

-record(llvm_br, {dst}).
-type llvm_br() :: #llvm_br{}.

-record(llvm_br_cond, {'cond', true_label, false_label, meta=[]}).
-type llvm_br_cond() :: #llvm_br_cond{}.

-record(llvm_indirectbr, {type, address, label_list}).
-type llvm_indirectbr() :: #llvm_indirectbr{}.

-record(llvm_switch, {type, value, default_label, value_label_list=[]}).
-type llvm_switch() :: #llvm_switch{}.

-record(llvm_invoke, {dst, cconv=[], ret_attrs=[], type, fnptrval, arglist=[],
                      fn_attrs=[], to_label, unwind_label}).
-type llvm_invoke() :: #llvm_invoke{}.

%% Binary Operations
-record(llvm_operation, {dst, op, type, src1, src2, options=[]}).
-type llvm_operation() :: #llvm_operation{}.

%% Aggregate Operations
-record(llvm_extractvalue, {dst, type, val, idx, idxs=[]}).
-type llvm_extractvalue() :: #llvm_extractvalue{}.

-record(llvm_insertvalue, {dst, val_type, val, elem_type, elem, idx, idxs=[]}).
-type llvm_insertvalue() :: #llvm_insertvalue{}.

%% Memory Access and Addressing Operations
-record(llvm_alloca, {dst, type, num=[], align=[]}).
-type llvm_alloca() :: #llvm_alloca{}.

-record(llvm_load, {dst, p_type, pointer, alignment=[], nontemporal=[],
                    volatile=false}).
-type llvm_load() :: #llvm_load{}.

-record(llvm_store, {type, value, p_type, pointer, alignment=[],
                     nontemporal=[], volatile=false}).
-type llvm_store() :: #llvm_store{}.

-record(llvm_getelementptr, {dst, p_type, value, typed_idxs, inbounds}).
-type llvm_getelementptr() :: #llvm_getelementptr{}.

%% Conversion Operations
-record(llvm_conversion, {dst, op, src_type, src, dst_type}).
-type llvm_conversion() :: #llvm_conversion{}.

-record(llvm_sitofp, {dst, src_type, src, dst_type}).
-type llvm_sitofp() :: #llvm_sitofp{}.

-record(llvm_ptrtoint, {dst, src_type, src, dst_type}).
-type llvm_ptrtoint() :: #llvm_ptrtoint{}.

-record(llvm_inttoptr, {dst, src_type, src, dst_type}).
-type llvm_inttoptr() :: #llvm_inttoptr{}.

%% Other Operations
-record(llvm_icmp, {dst, 'cond', type, src1, src2}).
-type llvm_icmp() :: #llvm_icmp{}.

-record(llvm_fcmp, {dst, 'cond', type, src1, src2}).
-type llvm_fcmp() :: #llvm_fcmp{}.

-record(llvm_phi, {dst, type, value_label_list}). 
-type llvm_phi() :: #llvm_phi{}.

-record(llvm_select, {dst, 'cond', typ1, val1, typ2, val2}).
-type llvm_select() :: #llvm_select{}.

-record(llvm_call, {dst=[], is_tail = false, cconv = [], ret_attrs = [], type,
                    fnptrval, arglist = [], fn_attrs = []}).
-type llvm_call() :: #llvm_call{}.

-record(llvm_fun_def, {linkage=[], visibility=[], cconv=[], ret_attrs=[],
    type, 'name', arglist=[], fn_attrs=[], align=[], body=[]}).
-type llvm_fun_def() :: #llvm_fun_def{}.

-record(llvm_fun_decl, {linkage=[], visibility=[], cconv=[], ret_attrs=[],
    type, 'name', arglist=[],  align=[]}).
-type llvm_fun_decl() :: #llvm_fun_decl{}.

-record(llvm_landingpad, {}).
-type llvm_landingpad() :: #llvm_landingpad{}.

-record(llvm_comment, {text}).
-type llvm_comment() :: #llvm_comment{}.

-record(llvm_label, {label}).
-type llvm_label() :: #llvm_label{}.

-record(llvm_const_decl, {dst, decl_type, type, value}).
-type llvm_const_decl() :: #llvm_const_decl{}.

-record(llvm_asm, {instruction}).
-type llvm_asm() :: #llvm_asm{}.

-record(llvm_adj_stack, {offset, 'register', type}).
-type llvm_adj_stack() :: #llvm_adj_stack{}.

-record(llvm_branch_meta, {id, true_weight, false_weight}).
-type llvm_branch_meta() :: #llvm_branch_meta{}.

%% Types
-record(llvm_void, {}).
-type llvm_void() :: #llvm_void{}.

-record(llvm_label_type, {}).
-type llvm_label_type() :: #llvm_label_type{}.

-record(llvm_int, {width}).
-type llvm_int() :: #llvm_int{}.

-record(llvm_float, {}).
-type llvm_float() :: #llvm_float{}.

-record(llvm_double, {}).
-type llvm_double() :: #llvm_double{}.

-record(llvm_fp80, {}).
-type llvm_fp80() :: #llvm_fp80{}.

-record(llvm_fp128, {}).
-type llvm_fp128() :: #llvm_fp128{}.

-record(llvm_ppc_fp128, {}).
-type llvm_ppc_fp128() :: #llvm_ppc_fp128{}.

-record(llvm_pointer, {type}).
-type llvm_pointer() :: #llvm_pointer{}.

-record(llvm_vector, {'size', type}).
-type llvm_vector() :: #llvm_vector{}.

-record(llvm_struct, {type_list}).
-type llvm_struct() :: #llvm_struct{}.

-record(llvm_array, {'size', type}).
-type llvm_array() :: #llvm_array{}.

-record(llvm_fun, {ret_type, arg_type_list}).
-type llvm_fun() :: #llvm_fun{}.
