%% -*- erlang-indent-level: 2 -*-

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%%
%% Provides abstract datatypes for LLVM Assembly.
%%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%---------------------------------------------------------------------

%% Terminator Instructions
-record(llvm_ret, {ret_list=[]}).
-record(llvm_br, {dst}).
-record(llvm_br_cond, {'cond', true_label, false_label}).
-record(llvm_switch, {type, value, default_label, value_label_list=[]}).
-record(llvm_invoke, {dst, cconv=[], ret_attrs=[], type, fnptrval, arglist=[],
    fn_attrs=[], to_label, unwind_label}).
%% Binary Operations
-record(llvm_operation, {dst, op, type, src1, src2, options=[]}).
%-record(llvm_add, {dst, type, src1, src2, options=[]}).
%-record(llvm_fadd, {dst, type, src1, src2, options=[]}).
%-record(llvm_sub, {dst, type, src1, src2, options=[]}).
%-record(llvm_fsub, {dst, type, src1, src2, options=[]}).
%-record(llvm_mul, {dst, type, src1, src2, options=[]}).
%-record(llvm_fmul, {dst, type, src1, src2, options=[]}).
%-record(llvm_udiv, {dst, type, src1, src2, options=[]}).
%-record(llvm_sdiv, {dst, type, src1, src2, options=[]}).
%-record(llvm_fdiv, {dst, type, src1, src2, options=[]}).
%-record(llvm_urem, {dst, type, src1, src2, options=[]}).
%-record(llvm_srem, {dst, type, src1, src2, options=[]}).
%-record(llvm_frem, {dst, type, src1, src2, options=[]}).
%%% Bitwise Binary Operations
%-record(llvm_shl, {dst, type, src1, src2, options=[]}).
%-record(llvm_lshr, {dst, type, src1, src2, options=[]}).
%-record(llvm_ashr ,{dst, type, src1, src2, options=[]}).
%-record(llvm_and,{dst, type, src1, src2}).
%-record(llvm_or, {dst, type, src1, src2}).
%-record(llvm_xor, {dst, type, src1, src2}).
%% Aggregate Operations
-record(llvm_extractvalue, {dst, type, val, idx, idxs=[]}).
%% Memory Access And Addressing Operations
-record(llvm_alloca, {dst, type, num = [], align = []}).
-record(llvm_load, {dst, p_type, pointer, alignment = [], nontemporal = [],
    volatile = false}).
-record(llvm_store, {type, value, p_type, pointer, alignment = [], nontemporal = [],
    volatile = false}).
-record(llvm_getelementptr, {dst, p_type, value, typed_idxs = [], inbounds = false}).
%% Conversion Operations
-record(llvm_conversion, {dst, op, src_type, src, dst_type}).
-record(llvm_sitofp, {dst, src_type, src, dst_type}).
-record(llvm_ptrtoint, {dst, src_type, src, dst_type}).
-record(llvm_inttoptr, {dst, src_type, src, dst_type}).
%% Other Operations
-record(llvm_icmp, {dst, 'cond', type, src1, src2}).
-record(llvm_fcmp, {dst, 'cond', type, src1, src2}).
-record(llvm_phi, {dst, type, value_label_list}). 
-record(llvm_select, {dst, 'cond', typ1, val1, typ2, val2}).
-record(llvm_call, {dst, is_tail = false, cconv = [], ret_attrs = [], type,
                    fnptrval, arglist = [], fn_attrs = []}).
-record(llvm_fun_def, {linkage=[], visibility=[], cconv=[], ret_attrs=[],
    type, 'name', arglist=[], fn_attrs=[], align=[], body=[]}).
-record(llvm_fun_decl, {linkage=[], visibility=[], cconv=[], ret_attrs=[],
    type, 'name', arglist=[],  align=[]}).
%%---------------------------------------------------------------------
-record(llvm_comment, {text}).
-record(llvm_label, {label}).
-record(llvm_const_decl, {dst, decl_type, type, value}).


%% Types
-record(llvm_void, {}).
-record(llvm_int, {width}).
-record(llvm_float, {}).
-record(llvm_double, {}).
-record(llvm_fp80, {}).
-record(llvm_fp128, {}).
-record(llvm_ppc_fp128, {}).
-record(llvm_pointer, {type}).
-record(llvm_vector, {'size', type}).
-record(llvm_struct, {type_list}).
-record(llvm_array, {'size', type}).
-record(llvm_fun, {ret_type, arg_type_list}).
