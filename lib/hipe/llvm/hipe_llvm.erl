%% -*- erlang-indent-level: 2 -*-
-module(hipe_llvm).

-export([
    mk_ret/1,
    ret_ret_list/1,

    mk_br/1,
    br_dst/1,

    mk_br_cond/3,
    br_cond_cond/1,
    br_cond_true_label/1,
    br_cond_false_label/1,

    mk_operation/6,
    operation_dst/1,
    operation_op/1,
    operation_type/1,
    operation_src1/1,
    operation_src2/1,
    operation_options/1,

%    mk_add/5,
%    add_dst/1,
%    add_type/1,
%    add_src1/1,
%    add_src2/1,
%    add_options/1,
%
%    mk_fadd/5,
%    fadd_dst/1,
%    fadd_type/1,
%    fadd_src1/1,
%    fadd_src2/1,
%    fadd_options/1,
%
%    mk_sub/5,
%    sub_dst/1,
%    sub_type/1,
%    sub_src1/1,
%    sub_src2/1,
%    sub_options/1,
%
%    mk_fsub/5,
%    fsub_dst/1,
%    fsub_type/1,
%    fsub_src1/1,
%    fsub_src2/1,
%    fsub_options/1,
%
%    mk_mul/5,
%    mul_dst/1,
%    mul_type/1,
%    mul_src1/1,
%    mul_src2/1,
%    mul_options/1,
%
%    mk_fmul/5,
%    fmul_dst/1,
%    fmul_type/1,
%    fmul_src1/1,
%    fmul_src2/1,
%    fmul_options/1,
%
%    mk_udiv/5,
%    udiv_dst/1,
%    udiv_type/1,
%    udiv_src1/1,
%    udiv_src2/1,
%    udiv_options/1,
%
%    mk_sdiv/5,
%    sdiv_dst/1,
%    sdiv_type/1,
%    sdiv_src1/1,
%    sdiv_src2/1,
%    sdiv_options/1,
%
%    mk_fdiv/5,
%    fdiv_dst/1,
%    fdiv_type/1,
%    fdiv_src1/1,
%    fdiv_src2/1,
%    fdiv_options/1,
%
%    mk_urem/5,
%    urem_dst/1,
%    urem_type/1,
%    urem_src1/1,
%    urem_src2/1,
%    urem_options/1,
%
%    mk_srem/5,
%    srem_dst/1,
%    srem_type/1,
%    srem_src1/1,
%    srem_src2/1,
%    srem_options/1,
%
%    mk_frem/5,
%    frem_dst/1,
%    frem_type/1,
%    frem_src1/1,
%    frem_src2/1,
%    frem_options/1,
%
%    mk_shl/5,
%    shl_dst/1,
%    shl_type/1,
%    shl_src1/1,
%    shl_src2/1,
%    shl_options/1,
%
%    mk_lshr/5,
%    lshr_dst/1,
%    lshr_type/1,
%    lshr_src1/1,
%    lshr_src2/1,
%    lshr_options/1,
%
%    mk_ashr/5,
%    ashr_dst/1,
%    ashr_type/1,
%    ashr_src1/1,
%    ashr_src2/1,
%    ashr_options/1,
%
%    mk_and/4,
%    and_dst/1,
%    and_type/1,
%    and_src1/1,
%    and_src2/1,
%
%    mk_or/4,
%    or_dst/1,
%    or_type/1,
%    or_src1/1,
%    or_src2/1,
%
%    mk_xor/4,
%    xor_dst/1,
%    xor_type/1,
%    xor_src1/1,
%    xor_src2/1,

    mk_extractvalue/5,
    extractvalue_dst/1,
    extractvalue_type/1,
    extractvalue_val/1,
    extractvalue_idx/1,
    extractvalue_idxs/1,

    mk_alloca/4,
    alloca_dst/1,
    alloca_type/1,
    alloca_num/1,
    alloca_align/1,

    mk_load/6,
    load_dst/1,
    load_p_type/1,
    load_pointer/1,
    load_alignment/1,
    load_nontemporal/1,
    load_volatile/1,

    mk_store/7,
    store_type/1,
    store_value/1,
    store_p_type/1,
    store_pointer/1,
    store_alignment/1,
    store_nontemporal/1,
    store_volatile/1,

    mk_getelementptr/5,
    getelementptr_dst/1,
    getelementptr_p_type/1,
    getelementptr_value/1,
    getelementptr_typed_idxs/1,
    getelementptr_inbounds/1,

    mk_ptrtoint/4,
    ptrtoint_dst/1,
    ptrtoint_src_type/1,
    ptrtoint_src/1,
    ptrtoint_dst_type/1,

    mk_inttoptr/4,
    inttoptr_dst/1,
    inttoptr_src_type/1,
    inttoptr_src/1,
    inttoptr_dst_type/1,

    mk_icmp/5,
    icmp_dst/1,
    icmp_cond/1,
    icmp_type/1,
    icmp_src1/1,
    icmp_src2/1,

    mk_fcmp/5,
    fcmp_dst/1,
    fcmp_cond/1,
    fcmp_type/1,
    fcmp_src1/1,
    fcmp_src2/1,

    mk_phi/3,
    phi_dst/1,
    phi_type/1,
    phi_value_label_list/1,

    mk_call/8,
    call_dst/1,
    call_is_tail/1,
    call_cconv/1,
    call_ret_attrs/1,
    call_type/1,
    call_fnptrval/1,
    call_arglist/1,
    call_fn_attrs/1,

    mk_fun_def/10,
    fun_def_linkage/1,
    fun_def_visibility/1,
    fun_def_cconv/1,
    fun_def_ret_attrs/1,
    fun_def_type/1,
    fun_def_name/1,
    fun_def_arglist/1,
    fun_def_fn_attrs/1,
    fun_def_align/1,
    fun_def_body/1,
    
    mk_fun_decl/8,
    fun_decl_linkage/1,
    fun_decl_visibility/1,
    fun_decl_cconv/1,
    fun_decl_ret_attrs/1,
    fun_decl_type/1,
    fun_decl_name/1,
    fun_decl_arglist/1,
    fun_decl_align/1,

    mk_comment/1,
    comment_text/1,

    mk_label/1,
    label_label/1
  ]).


%% Types
-export([
    mk_int/1,
    int_width/1,

    mk_pointer/1,
    pointer_type/1,

    mk_array/2,
    array_size/1,
    array_type/1,

    mk_vector/2,
    vector_size/1,
    vector_type/1,

    mk_struct/1,
    struct_type_list/1,

    mk_fun/2,
    function_ret_type/1,
    function_arg_type_list/1
  ]).

-export([pp_ins_list/2, pp_ins/2]).


%%-----------------------------------------------------------------------------

-include("hipe_llvm.hrl").

%%-----------------------------------------------------------------------------


%%
%% ret
%% 
mk_ret(Ret_list) -> #llvm_ret{ret_list=Ret_list}.
ret_ret_list(#llvm_ret{ret_list=Ret_list}) -> Ret_list.

%%
%% br
%%
mk_br(Dst) -> #llvm_br{dst=Dst}.
br_dst(#llvm_br{dst=Dst}) -> Dst.


%%
%% br_cond
%%
mk_br_cond(Cond, True_label, False_label) -> 
  #llvm_br_cond{'cond'=Cond, true_label=True_label, false_label=False_label}.
br_cond_cond(#llvm_br_cond{'cond'=Cond}) -> Cond.
br_cond_true_label(#llvm_br_cond{true_label=True_label}) -> True_label.
br_cond_false_label(#llvm_br_cond{false_label=False_label}) -> 
  False_label.


%%
%% operation
%%
mk_operation(Dst, Op, Type, Src1, Src2, Options) ->
  #llvm_operation{dst=Dst, op=Op, type=Type, src1=Src1, src2=Src2, 
    options=Options}.
operation_dst(#llvm_operation{dst=Dst}) -> Dst.
operation_op(#llvm_operation{op=Op}) -> Op.
operation_type(#llvm_operation{type=Type}) -> Type.
operation_src1(#llvm_operation{src1=Src1}) -> Src1.
operation_src2(#llvm_operation{src2=Src2}) -> Src2.
operation_options(#llvm_operation{options=Options}) -> Options.
%%%
%%% add
%%%
%mk_add(Dst, Type, Src1, Src2, Options) ->
%  #llvm_add{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%add_dst(#llvm_add{dst=Dst}) -> Dst.
%add_type(#llvm_add{type=Type}) -> Type.
%add_src1(#llvm_add{src1=Src1}) -> Src1.
%add_src2(#llvm_add{src2=Src2}) -> Src2.
%add_options(#llvm_add{options=Options}) -> Options.
%
%%%
%%% fadd
%%%
%mk_fadd(Dst, Type, Src1, Src2, Options) ->
%  #llvm_fadd{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%fadd_dst(#llvm_fadd{dst=Dst}) -> Dst.
%fadd_type(#llvm_fadd{type=Type}) -> Type.
%fadd_src1(#llvm_fadd{src1=Src1}) -> Src1.
%fadd_src2(#llvm_fadd{src2=Src2}) -> Src2.
%fadd_options(#llvm_fadd{options=Options}) -> Options.
%
%%%
%%% sub
%%%
%mk_sub(Dst, Type, Src1, Src2, Options) ->
%  #llvm_sub{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%sub_dst(#llvm_sub{dst=Dst}) -> Dst.
%sub_type(#llvm_sub{type=Type}) -> Type.
%sub_src1(#llvm_sub{src1=Src1}) -> Src1.
%sub_src2(#llvm_sub{src2=Src2}) -> Src2.
%sub_options(#llvm_sub{options=Options}) -> Options.
%
%%%
%%% fsub
%%%
%mk_fsub(Dst, Type, Src1, Src2, Options) ->
%  #llvm_fsub{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%fsub_dst(#llvm_fsub{dst=Dst}) -> Dst.
%fsub_type(#llvm_fsub{type=Type}) -> Type.
%fsub_src1(#llvm_fsub{src1=Src1}) -> Src1.
%fsub_src2(#llvm_fsub{src2=Src2}) -> Src2.
%fsub_options(#llvm_fsub{options=Options}) -> Options.
%
%%%
%%% mul
%%%
%mk_mul(Dst, Type, Src1, Src2, Options) ->
%  #llvm_mul{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%mul_dst(#llvm_mul{dst=Dst}) -> Dst.
%mul_type(#llvm_mul{type=Type}) -> Type.
%mul_src1(#llvm_mul{src1=Src1}) -> Src1.
%mul_src2(#llvm_mul{src2=Src2}) -> Src2.
%mul_options(#llvm_mul{options=Options}) -> Options.
%
%%%
%%% fmul
%%%
%mk_fmul(Dst, Type, Src1, Src2, Options) ->
%  #llvm_fmul{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%fmul_dst(#llvm_fmul{dst=Dst}) -> Dst.
%fmul_type(#llvm_fmul{type=Type}) -> Type.
%fmul_src1(#llvm_fmul{src1=Src1}) -> Src1.
%fmul_src2(#llvm_fmul{src2=Src2}) -> Src2.
%fmul_options(#llvm_fmul{options=Options}) -> Options.
%
%%%
%%% udiv
%%%
%mk_udiv(Dst, Type, Src1, Src2, Options) ->
%  #llvm_udiv{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%udiv_dst(#llvm_udiv{dst=Dst}) -> Dst.
%udiv_type(#llvm_udiv{type=Type}) -> Type.
%udiv_src1(#llvm_udiv{src1=Src1}) -> Src1.
%udiv_src2(#llvm_udiv{src2=Src2}) -> Src2.
%udiv_options(#llvm_udiv{options=Options}) -> Options.
%
%%%
%%% sdiv
%%%
%mk_sdiv(Dst, Type, Src1, Src2, Options) ->
%  #llvm_sdiv{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%sdiv_dst(#llvm_sdiv{dst=Dst}) -> Dst.
%sdiv_type(#llvm_sdiv{type=Type}) -> Type.
%sdiv_src1(#llvm_sdiv{src1=Src1}) -> Src1.
%sdiv_src2(#llvm_sdiv{src2=Src2}) -> Src2.
%sdiv_options(#llvm_sdiv{options=Options}) -> Options.
%
%
%%%
%%% fdiv
%%%
%mk_fdiv(Dst, Type, Src1, Src2, Options) ->
%  #llvm_fdiv{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%fdiv_dst(#llvm_fdiv{dst=Dst}) -> Dst.
%fdiv_type(#llvm_fdiv{type=Type}) -> Type.
%fdiv_src1(#llvm_fdiv{src1=Src1}) -> Src1.
%fdiv_src2(#llvm_fdiv{src2=Src2}) -> Src2.
%fdiv_options(#llvm_fdiv{options=Options}) -> Options.
%
%%%
%%% urem
%%%
%mk_urem(Dst, Type, Src1, Src2, Options) ->
%  #llvm_urem{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%urem_dst(#llvm_urem{dst=Dst}) -> Dst.
%urem_type(#llvm_urem{type=Type}) -> Type.
%urem_src1(#llvm_urem{src1=Src1}) -> Src1.
%urem_src2(#llvm_urem{src2=Src2}) -> Src2.
%urem_options(#llvm_urem{options=Options}) -> Options.
%
%%%
%%% srem
%%%
%mk_srem(Dst, Type, Src1, Src2, Options) ->
%  #llvm_srem{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%srem_dst(#llvm_srem{dst=Dst}) -> Dst.
%srem_type(#llvm_srem{type=Type}) -> Type.
%srem_src1(#llvm_srem{src1=Src1}) -> Src1.
%srem_src2(#llvm_srem{src2=Src2}) -> Src2.
%srem_options(#llvm_srem{options=Options}) -> Options.
%
%%%
%%% frem
%%%
%mk_frem(Dst, Type, Src1, Src2, Options) ->
%  #llvm_frem{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%frem_dst(#llvm_frem{dst=Dst}) -> Dst.
%frem_type(#llvm_frem{type=Type}) -> Type.
%frem_src1(#llvm_frem{src1=Src1}) -> Src1.
%frem_src2(#llvm_frem{src2=Src2}) -> Src2.
%frem_options(#llvm_frem{options=Options}) -> Options.
%
%
%%%
%%% shl
%%%
%mk_shl(Dst, Type, Src1, Src2, Options) ->
%  #llvm_shl{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%shl_dst(#llvm_shl{dst=Dst}) -> Dst.
%shl_type(#llvm_shl{type=Type}) -> Type.
%shl_src1(#llvm_shl{src1=Src1}) -> Src1.
%shl_src2(#llvm_shl{src2=Src2}) -> Src2.
%shl_options(#llvm_shl{options=Options}) -> Options.
%
%%%
%%% lshr
%%%
%mk_lshr(Dst, Type, Src1, Src2, Options) ->
%  #llvm_lshr{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%lshr_dst(#llvm_lshr{dst=Dst}) -> Dst.
%lshr_type(#llvm_lshr{type=Type}) -> Type.
%lshr_src1(#llvm_lshr{src1=Src1}) -> Src1.
%lshr_src2(#llvm_lshr{src2=Src2}) -> Src2.
%lshr_options(#llvm_lshr{options=Options}) -> Options.
%
%%%
%%% ashr
%%%
%mk_ashr(Dst, Type, Src1, Src2, Options) ->
%  #llvm_ashr{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
%ashr_dst(#llvm_ashr{dst=Dst}) -> Dst.
%ashr_type(#llvm_ashr{type=Type}) -> Type.
%ashr_src1(#llvm_ashr{src1=Src1}) -> Src1.
%ashr_src2(#llvm_ashr{src2=Src2}) -> Src2.
%ashr_options(#llvm_ashr{options=Options}) -> Options.
%
%
%%%
%%% and
%%%
%mk_and(Dst, Type, Src1, Src2) ->
%  #llvm_and{dst=Dst, type=Type, src1=Src1, src2=Src2}.
%and_dst(#llvm_and{dst=Dst}) -> Dst.
%and_type(#llvm_and{type=Type}) -> Type.
%and_src1(#llvm_and{src1=Src1}) -> Src1.
%and_src2(#llvm_and{src2=Src2}) -> Src2.
%
%%%
%%% or
%%%
%mk_or(Dst, Type, Src1, Src2) ->
%  #llvm_or{dst=Dst, type=Type, src1=Src1, src2=Src2}.
%or_dst(#llvm_or{dst=Dst}) -> Dst.
%or_type(#llvm_or{type=Type}) -> Type.
%or_src1(#llvm_or{src1=Src1}) -> Src1.
%or_src2(#llvm_or{src2=Src2}) -> Src2.
%
%%%
%%% xor
%%%
%mk_xor(Dst, Type, Src1, Src2) ->
%  #llvm_xor{dst=Dst, type=Type, src1=Src1, src2=Src2}.
%xor_dst(#llvm_xor{dst=Dst}) -> Dst.
%xor_type(#llvm_xor{type=Type}) -> Type.
%xor_src1(#llvm_xor{src1=Src1}) -> Src1.
%xor_src2(#llvm_xor{src2=Src2}) -> Src2.
%
%%
%% extractvalue
%%
mk_extractvalue(Dst, Type, Val, Idx, Idxs) ->
  #llvm_extractvalue{dst=Dst,type=Type,val=Val,idx=Idx,idxs=Idxs}.
extractvalue_dst(#llvm_extractvalue{dst=Dst})-> Dst.
extractvalue_type(#llvm_extractvalue{type=Type})-> Type.
extractvalue_val(#llvm_extractvalue{val=Val})-> Val.
extractvalue_idx(#llvm_extractvalue{idx=Idx})-> Idx.
extractvalue_idxs(#llvm_extractvalue{idxs=Idxs})-> Idxs.

%%
%% alloca
%%
mk_alloca(Dst, Type, Num, Align) ->
  #llvm_alloca{dst=Dst, type=Type, num=Num, align=Align}.
alloca_dst(#llvm_alloca{dst=Dst}) -> Dst.
alloca_type(#llvm_alloca{type=Type})-> Type.
alloca_num(#llvm_alloca{num=Num})-> Num.
alloca_align(#llvm_alloca{align=Align})-> Align.

%%
%% load
%%
mk_load(Dst, Type, Pointer, Alignment, Nontemporal, Volatile) ->
  #llvm_load{dst=Dst, p_type=Type, pointer=Pointer, alignment=Alignment,
    nontemporal=Nontemporal, volatile=Volatile}.
load_dst(#llvm_load{dst=Dst})-> Dst.
load_p_type(#llvm_load{p_type=Type})-> Type.
load_pointer(#llvm_load{pointer=Pointer})-> Pointer.
load_alignment(#llvm_load{alignment=Alignment})-> Alignment.
load_nontemporal(#llvm_load{nontemporal=Nontemporal})-> Nontemporal.
load_volatile(#llvm_load{volatile=Volatile})-> Volatile.

%%
%% store
%%
mk_store(Type, Value, P_Type, Pointer, Alignment, Nontemporal, Volatile) ->
  #llvm_store{type=Type, value=Value, p_type=P_Type, pointer=Pointer, alignment=Alignment,
    nontemporal=Nontemporal, volatile=Volatile}.
store_type(#llvm_store{type=Type})-> Type.
store_value(#llvm_store{value=Value})-> Value.
store_p_type(#llvm_store{p_type=P_Type})-> P_Type.
store_pointer(#llvm_store{pointer=Pointer})-> Pointer.
store_alignment(#llvm_store{alignment=Alignment})-> Alignment.
store_nontemporal(#llvm_store{nontemporal=Nontemporal})-> Nontemporal.
store_volatile(#llvm_store{volatile=Volatile})-> Volatile.

%%
%% getelementptr
%%
mk_getelementptr(Dst, P_Type, Value, Typed_Idxs, Inbounds) ->
  #llvm_getelementptr{dst=Dst,p_type=P_Type, value=Value, typed_idxs=Typed_Idxs,
    inbounds=Inbounds}.
getelementptr_dst(#llvm_getelementptr{dst=Dst}) -> Dst. 
getelementptr_p_type(#llvm_getelementptr{p_type=P_Type}) -> P_Type.
getelementptr_value(#llvm_getelementptr{value=Value}) -> Value.
getelementptr_typed_idxs(#llvm_getelementptr{typed_idxs=Typed_Idxs}) -> Typed_Idxs.
getelementptr_inbounds(#llvm_getelementptr{inbounds=Inbounds}) -> Inbounds.
%%
%% ptrtoint
%%
mk_ptrtoint(Dst, Src_Type, Src, Dst_Type) ->
  #llvm_ptrtoint{dst=Dst, src_type=Src_Type, src=Src, dst_type=Dst_Type}.
ptrtoint_dst(#llvm_ptrtoint{dst=Dst}) -> Dst.
ptrtoint_src_type(#llvm_ptrtoint{src_type=Src_Type}) -> Src_Type.
ptrtoint_src(#llvm_ptrtoint{src=Src}) -> Src.
ptrtoint_dst_type(#llvm_ptrtoint{dst_type=Dst_Type}) -> Dst_Type .

%%
%% inttoptr
%%
mk_inttoptr(Dst, Src_Type, Src, Dst_Type) ->
  #llvm_inttoptr{dst=Dst, src_type=Src_Type, src=Src, dst_type=Dst_Type}.
inttoptr_dst(#llvm_inttoptr{dst=Dst}) -> Dst.
inttoptr_src_type(#llvm_inttoptr{src_type=Src_Type}) -> Src_Type.
inttoptr_src(#llvm_inttoptr{src=Src}) -> Src.
inttoptr_dst_type(#llvm_inttoptr{dst_type=Dst_Type}) -> Dst_Type .

%%
%% icmp
%%
mk_icmp(Dst, Cond, Type, Src1, Src2) ->
  #llvm_icmp{dst=Dst,'cond'=Cond,type=Type,src1=Src1,src2=Src2}.
icmp_dst(#llvm_icmp{dst=Dst}) -> Dst.
icmp_cond(#llvm_icmp{'cond'=Cond}) -> Cond.
icmp_type(#llvm_icmp{type=Type}) -> Type.
icmp_src1(#llvm_icmp{src1=Src1}) -> Src1.
icmp_src2(#llvm_icmp{src2=Src2}) -> Src2.

%%
%% fcmp
%%
mk_fcmp(Dst, Cond, Type, Src1, Src2) ->
  #llvm_fcmp{dst=Dst,'cond'=Cond,type=Type,src1=Src1,src2=Src2}.
fcmp_dst(#llvm_fcmp{dst=Dst}) -> Dst.
fcmp_cond(#llvm_fcmp{'cond'=Cond}) -> Cond.
fcmp_type(#llvm_fcmp{type=Type}) -> Type.
fcmp_src1(#llvm_fcmp{src1=Src1}) -> Src1.
fcmp_src2(#llvm_fcmp{src2=Src2}) -> Src2.

%%
%% phi
%%
mk_phi(Dst, Type, Value_label_list) ->
  #llvm_phi{dst=Dst, type=Type,value_label_list=Value_label_list}.
phi_dst(#llvm_phi{dst=Dst}) -> Dst.
phi_type(#llvm_phi{type=Type}) -> Type.
phi_value_label_list(#llvm_phi{value_label_list=Value_label_list}) ->
  Value_label_list.

%%
%% call
%%
mk_call(Dst, Is_tail, Cconv, Ret_attrs, Type, Fnptrval, Arglist, Fn_attrs) ->
  #llvm_call{dst=Dst, is_tail=Is_tail, cconv=Cconv, ret_attrs=Ret_attrs, 
    type=Type, fnptrval=Fnptrval, arglist=Arglist, fn_attrs=Fn_attrs}.
call_dst(#llvm_call{dst=Dst}) -> Dst.
call_is_tail(#llvm_call{is_tail=Is_tail}) -> Is_tail.
call_cconv(#llvm_call{cconv=Cconv}) -> Cconv.
call_ret_attrs(#llvm_call{ret_attrs=Ret_attrs}) -> Ret_attrs.
call_type(#llvm_call{type=Type}) -> Type.
call_fnptrval(#llvm_call{fnptrval=Fnptrval}) -> Fnptrval.
call_arglist(#llvm_call{arglist=Arglist}) -> Arglist.
call_fn_attrs(#llvm_call{fn_attrs=Fn_attrs}) -> Fn_attrs.

%% 
%% fun_def
%%
mk_fun_def(Linkage, Visibility, Cconv, Ret_attrs, Type, Name, Arglist,
  Fn_attrs, Align, Body)->
  #llvm_fun_def{
    linkage=Linkage,
    visibility=Visibility,
    cconv=Cconv,
    ret_attrs=Ret_attrs,
    type=Type,
    'name'=Name,
    arglist=Arglist,
    fn_attrs=Fn_attrs,
    align=Align,
    body=Body
  }.

fun_def_linkage(#llvm_fun_def{linkage=Linkage}) -> Linkage.
fun_def_visibility(#llvm_fun_def{visibility=Visibility}) -> Visibility.
fun_def_cconv(#llvm_fun_def{cconv=Cconv}) -> Cconv .
fun_def_ret_attrs(#llvm_fun_def{ret_attrs=Ret_attrs}) -> Ret_attrs.
fun_def_type(#llvm_fun_def{type=Type}) -> Type.
fun_def_name(#llvm_fun_def{'name'=Name}) -> Name.
fun_def_arglist(#llvm_fun_def{arglist=Arglist}) -> Arglist.
fun_def_fn_attrs(#llvm_fun_def{fn_attrs=Fn_attrs}) -> Fn_attrs.
fun_def_align(#llvm_fun_def{align=Align}) -> Align.
fun_def_body(#llvm_fun_def{body=Body}) -> Body.


%% 
%% fun_decl
%%
mk_fun_decl(Linkage, Visibility, Cconv, Ret_attrs, Type, Name, Arglist, Align)->
  #llvm_fun_decl{
    linkage=Linkage,
    visibility=Visibility,
    cconv=Cconv,
    ret_attrs=Ret_attrs,
    type=Type,
    'name'=Name,
    arglist=Arglist,
    align=Align
  }.

fun_decl_linkage(#llvm_fun_decl{linkage=Linkage}) -> Linkage.
fun_decl_visibility(#llvm_fun_decl{visibility=Visibility}) -> Visibility.
fun_decl_cconv(#llvm_fun_decl{cconv=Cconv}) -> Cconv .
fun_decl_ret_attrs(#llvm_fun_decl{ret_attrs=Ret_attrs}) -> Ret_attrs.
fun_decl_type(#llvm_fun_decl{type=Type}) -> Type.
fun_decl_name(#llvm_fun_decl{'name'=Name}) -> Name.
fun_decl_arglist(#llvm_fun_decl{arglist=Arglist}) -> Arglist.
fun_decl_align(#llvm_fun_decl{align=Align}) -> Align.

%%
%% comment
%%
mk_comment(Text) -> #llvm_comment{text=Text}.
comment_text(#llvm_comment{text=Text}) -> Text.

%%
%% label
%%
mk_label(Label) -> #llvm_label{label=Label}.
label_label(#llvm_label{label=Label}) -> Label.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%
%% Types
%% 

mk_int(Width) -> #llvm_int{width=Width}.
int_width(#llvm_int{width=Width}) -> Width.

mk_pointer(Type) -> #llvm_pointer{type=Type}.
pointer_type(#llvm_pointer{type=Type}) -> Type.

mk_array(Size, Type) -> #llvm_array{'size'=Size, type=Type}.
array_size(#llvm_array{'size'=Size}) -> Size.
array_type(#llvm_array{type=Type}) -> Type.

mk_vector(Size, Type) -> #llvm_vector{'size'=Size, type=Type}.
vector_size(#llvm_vector{'size'=Size}) -> Size.
vector_type(#llvm_vector{type=Type}) -> Type.

mk_struct(Type_list) -> #llvm_struct{type_list=Type_list}.
struct_type_list(#llvm_struct{type_list=Type_list}) -> Type_list.

mk_fun(Ret_type, Arg_type_list) -> 
  #llvm_fun{ret_type=Ret_type, arg_type_list=Arg_type_list}.
function_ret_type(#llvm_fun{ret_type=Ret_type}) -> Ret_type.
function_arg_type_list(#llvm_fun{arg_type_list=Arg_type_list}) ->
  Arg_type_list.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


pp_ins_list(Dev, []) -> ok;
pp_ins_list(Dev, [I|Is]) ->
  pp_ins(Dev, I),
  pp_ins_list(Dev, Is).


pp_ins(Dev, I) ->
  case indent(I) of
    true ->  io:format(Dev, "  ", []);
    false -> ok
  end,
  case I of
    #llvm_ret{} ->
      io:format(Dev, "ret ", []),
      case ret_ret_list(I) of
        [] -> io:format(Dev, "void", []);
        List -> pp_args(Dev, List)
      end,
      io:format(Dev, "~n", []);
    #llvm_br{} ->
      io:format(Dev, "br label ~s~n", [br_dst(I)]);
    #llvm_br_cond{} ->
      io:format(Dev, "br i1 ~s, label ~s, label ~s~n", 
        [br_cond_cond(I), br_cond_true_label(I), br_cond_false_label(I)]);
    #llvm_operation{} ->
      io:format(Dev, "~s = ~s ", [operation_dst(I), operation_op(I)]),
      case op_has_options(operation_op(I)) of
        true -> pp_options(Dev, operation_options(I));
        false -> ok
      end,
      io:format(Dev, "~s ~s, ~s~n",
        [operation_type(I), operation_src1(I), operation_src2(I)]);
    #llvm_extractvalue{} ->
      io:format(Dev, "~s = extractvalue ~s ~s, ~s~n", 
        %%TODO Print idxs
        [extractvalue_dst(I), extractvalue_type(I), extractvalue_val(I),
          extractvalue_idx(I)]);
    #llvm_alloca{} ->
      io:format(Dev, "~s = alloca ~s ", [alloca_dst(I), alloca_type(I)]),
      case alloca_num(I) of
        [] -> ok;
        Num -> io:format(Dev, ",~s ~s ", [alloca_type(I), Num])
      end,
      case alloca_align(I) of
        [] ->ok;
        Align -> io:format(Dev, ",align ~s", [Align])
      end,
      io:format(Dev, "~n", []);
    #llvm_load{} ->
      io:format(Dev, "~s = ",[load_dst(I)]),
      case load_volatile(I) of
        true -> io:format(Dev, "volatile ", []);
        false -> ok
      end,
      io:format(Dev, "load ~s* ~s ", 
        [load_p_type(I), load_pointer(I)]),
      case load_alignment(I) of 
        [] -> ok;
        Al -> io:format(Dev, ", align ~s ", [Al])
      end,
      case load_nontemporal(I) of
        [] -> ok;
        In -> io:format(Dev, ", !nontemporal !~s", [In])
      end,
      io:format(Dev, "~n", []);
    #llvm_store{} ->
      case store_volatile(I) of
        true -> io:format(Dev, "volatile ", []);
        false -> ok
      end,
      io:format(Dev, "store ~s ~s, ~s* ~s ", 
        [store_type(I), store_value(I), store_p_type(I), store_pointer(I)]),
      case store_alignment(I) of 
        [] -> ok;
        Al -> io:format(Dev, ", align ~s ", [Al])
      end,
      case store_nontemporal(I) of
        [] -> ok;
        In -> io:format(Dev, ", !nontemporal !~s", [In])
      end,
      io:format(Dev, "~n", []);
    #llvm_getelementptr{} ->
      io:format(Dev, "~s = getelementptr ", [getelementptr_dst(I)]),
      case getelementptr_inbounds(I) of
        true -> io:format(Dev, "inbounds ", []);
        false -> ok
      end,
      io:format(Dev, "~s* ~s", [getelementptr_p_type(I), 
          getelementptr_value(I)]),
      pp_typed_idxs(Dev, getelementptr_typed_idxs(I)),
      io:format(Dev, "~n", []);
    #llvm_ptrtoint{} ->
      io:format(Dev, "~s = ptrtoint ~s* ~s to ~s~n", [ptrtoint_dst(I),
          ptrtoint_src_type(I), ptrtoint_src(I), ptrtoint_dst_type(I)]);
    #llvm_inttoptr{} ->
      io:format(Dev, "~s = inttoptr ~s ~s to ~s*~n", [inttoptr_dst(I),
          inttoptr_src_type(I), inttoptr_src(I), inttoptr_dst_type(I)]);
    #llvm_icmp{} ->
      io:format(Dev, "~s = icmp ~s ~s ~s, ~s~n",
        [icmp_dst(I), icmp_cond(I), icmp_type(I), icmp_src1(I), icmp_src2(I)]);
    #llvm_fcmp{} ->
      io:format(Dev, "~s = fcmp ~s ~s ~s, ~s~n",
        [fcmp_dst(I), fcmp_cond(I), fcmp_type(I), fcmp_src1(I), fcmp_src2(I)]);
    #llvm_phi{} ->
      io:format(Dev, "~s = phi ~s ", [phi_dst(I), phi_type(I)]),
      pp_phi_value_labels(Dev, phi_value_label_list(I)),
      io:format(Dev, "~n", []);
    #llvm_call{} ->
      io:format(Dev, "~s = ", [call_dst(I)]),
      case call_is_tail(I) of
        true -> io:format(Dev, "tail ", []);
        false -> ok
      end,
      io:format(Dev, "call ", []),
      io:format(Dev, "~s " , [call_cconv(I)]),
      pp_options(Dev, call_ret_attrs(I)),
      io:format(Dev, "~s ~s(", [call_type(I), call_fnptrval(I)]),
      pp_args(Dev, call_arglist(I)),
      io:format(Dev, ") ", []),
      pp_options(Dev, call_fn_attrs(I)),
      io:format(Dev, "~n", []);
    #llvm_fun_def{} ->
      io:format(Dev, "define ", []),
      pp_options(Dev, fun_def_linkage(I)),
      pp_options(Dev, fun_def_visibility(I)),
      case fun_def_cconv(I) of
        [] -> ok;
        Cc -> io:format(Dev, "~s ", [Cc])
      end,
      pp_options(Dev, fun_def_ret_attrs(I)),
      io:format(Dev, "~s @~s", [fun_def_type(I), fun_def_name(I)]),
      io:format(Dev, "(", []),
      pp_args(Dev, fun_def_arglist(I)),
      io:format(Dev, ") ", []),
      pp_options(Dev, fun_def_fn_attrs(I)),
      case fun_def_align(I) of
        [] -> ok;
        N -> io:format(Dev, "align ~s", [N])
      end,
      io:format(Dev, "{~n", []),
      pp_ins_list(Dev, fun_def_body(I)),
      io:format(Dev, "}~n", []);
    #llvm_fun_decl{} ->
      io:format(Dev, "declare ", []),
      pp_options(Dev, fun_decl_linkage(I)),
      pp_options(Dev, fun_decl_visibility(I)),
      case fun_decl_cconv(I) of
        [] -> ok;
        Cc -> io:format(Dev, "~s ", [Cc])
      end,
      pp_options(Dev, fun_decl_ret_attrs(I)),
      io:format(Dev, "~s @~s", [fun_decl_type(I), fun_decl_name(I)]),
      io:format(Dev, "(", []),
      pp_types(Dev, fun_decl_arglist(I)),
      io:format(Dev, ") ", []),
      case fun_decl_align(I) of
        [] -> ok;
        N -> io:format(Dev, "align ~s", [N])
      end,
      io:format(Dev, "~n", []);

    #llvm_comment{} ->
      io:format(Dev, "; ~s~n", [comment_text(I)]);
    #llvm_label{} ->
      io:format(Dev, "~s:~n", [label_label(I)]);

    Other -> exit({?MODULE, pp_ins, {"Unknown LLVM instruction", Other}})
  end.


pp_type_list(Dev, []) -> ok;
pp_type_list(Dev, [T]) ->
  pp_type(Dev, T);
pp_type_list(Dev, [T|Ts]) ->
  pp_type(Dev, T),
  io:format(Dev, ", ", []),
  pp_type_list(Dev, Ts).

pp_type(Dev, Type) ->
  case Type of 
    #llvm_void{} ->
      io:format(Dev, "void", []);
    %Integer
    #llvm_int{} ->
      io:format(Dev, "i~w", [int_width(Type)]);
    %Float
    #llvm_float{} ->
      io:format(Dev, "float", []);
    #llvm_double{} ->
      io:format(Dev, "double", []);
    #llvm_fp80{} ->
      io:format(Dev, "x86_fp80", []);
    #llvm_fp128{} ->
      io:format(Dev, "fp128", []);
    #llvm_ppc_fp128{} ->
      io:format(Dev, "ppc_fp128", []);
    %Pointer
    #llvm_pointer{} ->
      pp_type(Dev, pointer_type(Type)),
      io:format(Dev, "*", []);
    %Function
    #llvm_fun{} ->
      pp_type(Dev, function_ret_type(Type)),
      io:format(Dev, " ", []),
      io:format(Dev, "(", []),
      pp_type_list(Dev, function_arg_type_list(Type)),
      io:format(Dev, ")", []);
    %Aggregate
    #llvm_array{} ->
      io:format(Dev, "[~w x ", [array_size(Type)]),
      pp_type(Dev, array_type(Type)),
      io:format(Dev, "]", []);
    #llvm_struct{} ->
      io:format(Dev, "{", []),
      pp_type_list(Dev, struct_type_list(Type)),
      io:format(Dev, "}", []);
    #llvm_vector{} ->
      io:format(Dev, "{~w x ", [array_size(Type)]),
      pp_type(Dev, array_type(Type)),
      io:format(Dev, "}", [])
  end.


op_has_options(Op) ->
  case Op of
    'and' -> false;
    'or' -> false;
    'xor' -> false;
    _ -> true
  end.

pp_args(_Dev, []) -> ok;
pp_args(Dev, [{Type, Arg} | []]) ->
  io:format(Dev, "~s ~s", [Type, Arg]);
pp_args(Dev, [{Type, Arg} | Args]) ->
  io:format(Dev, "~s ~s, ", [Type, Arg]),
  pp_args(Dev, Args).

pp_types(_Dev, []) -> ok;
pp_types(Dev, [T | []]) ->
  io:format(Dev, "~s ", [T]);
pp_types(Dev, [T | Types]) ->
  io:format(Dev, "~s , ", [T]),
  pp_types(Dev, Types).


pp_options(_Dev, []) -> ok;
pp_options(Dev, [O|Os])-> io:format(Dev,"~s ", [erlang:atom_to_list(O)]),
  pp_options(Dev, Os).

pp_phi_value_labels(_Dev, []) -> ok;
pp_phi_value_labels(Dev, [{Value, Label}|[]]) ->
  io:format(Dev, "[ ~s, ~s ]", [Value, Label]);
pp_phi_value_labels(Dev,[{Value,Label}| VL]) ->
  io:format(Dev, "[ ~s, ~s ], ", [Value, Label]),
  pp_phi_value_labels(Dev, VL).


pp_typed_idxs(_Dev, []) -> ok;
pp_typed_idxs(Dev, [{Type, Id} | Tids]) ->
  io:format(Dev, ", ~s ~s", [Type, Id]),
  pp_typed_idxs(Dev, Tids).

indent(I) ->
  case I of 
    #llvm_label{} -> false;
    #llvm_fun_def{} -> false;
    #llvm_fun_decl{} -> false;
    _ -> true
  end.
