%% -*- erlang-indent-level: 2 -*-

-module(hipe_llvm).

-export([
    mk_ret/2,
    ret_type/1,
    ret_value/1,

    mk_br/1,
    br_dst/1,

    mk_br_cond/3,
    br_cond_cond/1,
    br_cond_true_label/1,
    br_cond_false_label/1,

    mk_add/5,
    add_dst/1,
    add_type/1,
    add_src1/1,
    add_src2/1,
    add_options/1,

    mk_fadd/5,
    fadd_dst/1,
    fadd_type/1,
    fadd_src1/1,
    fadd_src2/1,
    fadd_options/1,

    mk_sub/5,
    sub_dst/1,
    sub_type/1,
    sub_src1/1,
    sub_src2/1,
    sub_options/1,

    mk_fsub/5,
    fsub_dst/1,
    fsub_type/1,
    fsub_src1/1,
    fsub_src2/1,
    fsub_options/1,

    mk_mul/5,
    mul_dst/1,
    mul_type/1,
    mul_src1/1,
    mul_src2/1,
    mul_options/1,

    mk_fmul/5,
    fmul_dst/1,
    fmul_type/1,
    fmul_src1/1,
    fmul_src2/1,
    fmul_options/1,

    mk_udiv/5,
    udiv_dst/1,
    udiv_type/1,
    udiv_src1/1,
    udiv_src2/1,
    udiv_options/1,

    mk_sdiv/5,
    sdiv_dst/1,
    sdiv_type/1,
    sdiv_src1/1,
    sdiv_src2/1,
    sdiv_options/1,

    mk_fdiv/5,
    fdiv_dst/1,
    fdiv_type/1,
    fdiv_src1/1,
    fdiv_src2/1,
    fdiv_options/1,

    mk_urem/5,
    urem_dst/1,
    urem_type/1,
    urem_src1/1,
    urem_src2/1,
    urem_options/1,

    mk_srem/5,
    srem_dst/1,
    srem_type/1,
    srem_src1/1,
    srem_src2/1,
    srem_options/1,

    mk_frem/5,
    frem_dst/1,
    frem_type/1,
    frem_src1/1,
    frem_src2/1,
    frem_options/1,

    mk_shl/5,
    shl_dst/1,
    shl_type/1,
    shl_src1/1,
    shl_src2/1,
    shl_options/1,
    
    mk_lshr/5,
    lshr_dst/1,
    lshr_type/1,
    lshr_src1/1,
    lshr_src2/1,
    lshr_options/1,

    mk_ashr/5,
    ashr_dst/1,
    ashr_type/1,
    ashr_src1/1,
    ashr_src2/1,
    ashr_options/1,

    mk_and/4,
    and_dst/1,
    and_type/1,
    and_src1/1,
    and_src2/1,

    mk_or/4,
    or_dst/1,
    or_type/1,
    or_src1/1,
    or_src2/1,

    mk_xor/4,
    xor_dst/1,
    xor_type/1,
    xor_src1/1,
    xor_src2/1,

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
    load_type/1,
    load_pointer/1,
    load_alignment/1,
    load_nontemporal/1,
    load_volatile/1,

    mk_store/6,
    store_dst/1,
    store_type/1,
    store_pointer/1,
    store_alignment/1,
    store_nontemporal/1,
    store_volatile/1,

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
    phi_value_label_list/1
  ]).

-export([pp_ins/2]).


%%-----------------------------------------------------------------------------

-include("hipe_llvm.hrl").

%%-----------------------------------------------------------------------------


%%
%% ret
%% 
mk_ret(Type, Value) -> #llvm_ret{type=Type, value=Value}.
ret_type(#llvm_ret{type=Type}) -> Type.
ret_value(#llvm_ret{value=Value}) -> Value.

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
%% add
%%
mk_add(Dst, Type, Src1, Src2, Options) ->
  #llvm_add{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
add_dst(#llvm_add{dst=Dst}) -> Dst.
add_type(#llvm_add{type=Type}) -> Type.
add_src1(#llvm_add{src1=Src1}) -> Src1.
add_src2(#llvm_add{src2=Src2}) -> Src2.
add_options(#llvm_add{options=Options}) -> Options.

%%
%% fadd
%%
mk_fadd(Dst, Type, Src1, Src2, Options) ->
  #llvm_fadd{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
fadd_dst(#llvm_fadd{dst=Dst}) -> Dst.
fadd_type(#llvm_fadd{type=Type}) -> Type.
fadd_src1(#llvm_fadd{src1=Src1}) -> Src1.
fadd_src2(#llvm_fadd{src2=Src2}) -> Src2.
fadd_options(#llvm_fadd{options=Options}) -> Options.

%%
%% sub
%%
mk_sub(Dst, Type, Src1, Src2, Options) ->
  #llvm_sub{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
sub_dst(#llvm_sub{dst=Dst}) -> Dst.
sub_type(#llvm_sub{type=Type}) -> Type.
sub_src1(#llvm_sub{src1=Src1}) -> Src1.
sub_src2(#llvm_sub{src2=Src2}) -> Src2.
sub_options(#llvm_sub{options=Options}) -> Options.

%%
%% fsub
%%
mk_fsub(Dst, Type, Src1, Src2, Options) ->
  #llvm_fsub{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
fsub_dst(#llvm_fsub{dst=Dst}) -> Dst.
fsub_type(#llvm_fsub{type=Type}) -> Type.
fsub_src1(#llvm_fsub{src1=Src1}) -> Src1.
fsub_src2(#llvm_fsub{src2=Src2}) -> Src2.
fsub_options(#llvm_fsub{options=Options}) -> Options.

%%
%% mul
%%
mk_mul(Dst, Type, Src1, Src2, Options) ->
  #llvm_mul{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
mul_dst(#llvm_mul{dst=Dst}) -> Dst.
mul_type(#llvm_mul{type=Type}) -> Type.
mul_src1(#llvm_mul{src1=Src1}) -> Src1.
mul_src2(#llvm_mul{src2=Src2}) -> Src2.
mul_options(#llvm_mul{options=Options}) -> Options.

%%
%% fmul
%%
mk_fmul(Dst, Type, Src1, Src2, Options) ->
  #llvm_fmul{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
fmul_dst(#llvm_fmul{dst=Dst}) -> Dst.
fmul_type(#llvm_fmul{type=Type}) -> Type.
fmul_src1(#llvm_fmul{src1=Src1}) -> Src1.
fmul_src2(#llvm_fmul{src2=Src2}) -> Src2.
fmul_options(#llvm_fmul{options=Options}) -> Options.

%%
%% udiv
%%
mk_udiv(Dst, Type, Src1, Src2, Options) ->
  #llvm_udiv{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
udiv_dst(#llvm_udiv{dst=Dst}) -> Dst.
udiv_type(#llvm_udiv{type=Type}) -> Type.
udiv_src1(#llvm_udiv{src1=Src1}) -> Src1.
udiv_src2(#llvm_udiv{src2=Src2}) -> Src2.
udiv_options(#llvm_udiv{options=Options}) -> Options.

%%
%% sdiv
%%
mk_sdiv(Dst, Type, Src1, Src2, Options) ->
  #llvm_sdiv{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
sdiv_dst(#llvm_sdiv{dst=Dst}) -> Dst.
sdiv_type(#llvm_sdiv{type=Type}) -> Type.
sdiv_src1(#llvm_sdiv{src1=Src1}) -> Src1.
sdiv_src2(#llvm_sdiv{src2=Src2}) -> Src2.
sdiv_options(#llvm_sdiv{options=Options}) -> Options.


%%
%% fdiv
%%
mk_fdiv(Dst, Type, Src1, Src2, Options) ->
  #llvm_fdiv{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
fdiv_dst(#llvm_fdiv{dst=Dst}) -> Dst.
fdiv_type(#llvm_fdiv{type=Type}) -> Type.
fdiv_src1(#llvm_fdiv{src1=Src1}) -> Src1.
fdiv_src2(#llvm_fdiv{src2=Src2}) -> Src2.
fdiv_options(#llvm_fdiv{options=Options}) -> Options.

%%
%% urem
%%
mk_urem(Dst, Type, Src1, Src2, Options) ->
  #llvm_urem{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
urem_dst(#llvm_urem{dst=Dst}) -> Dst.
urem_type(#llvm_urem{type=Type}) -> Type.
urem_src1(#llvm_urem{src1=Src1}) -> Src1.
urem_src2(#llvm_urem{src2=Src2}) -> Src2.
urem_options(#llvm_urem{options=Options}) -> Options.

%%
%% srem
%%
mk_srem(Dst, Type, Src1, Src2, Options) ->
  #llvm_srem{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
srem_dst(#llvm_srem{dst=Dst}) -> Dst.
srem_type(#llvm_srem{type=Type}) -> Type.
srem_src1(#llvm_srem{src1=Src1}) -> Src1.
srem_src2(#llvm_srem{src2=Src2}) -> Src2.
srem_options(#llvm_srem{options=Options}) -> Options.

%%
%% frem
%%
mk_frem(Dst, Type, Src1, Src2, Options) ->
  #llvm_frem{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
frem_dst(#llvm_frem{dst=Dst}) -> Dst.
frem_type(#llvm_frem{type=Type}) -> Type.
frem_src1(#llvm_frem{src1=Src1}) -> Src1.
frem_src2(#llvm_frem{src2=Src2}) -> Src2.
frem_options(#llvm_frem{options=Options}) -> Options.


%%
%% shl
%%
mk_shl(Dst, Type, Src1, Src2, Options) ->
  #llvm_shl{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
shl_dst(#llvm_shl{dst=Dst}) -> Dst.
shl_type(#llvm_shl{type=Type}) -> Type.
shl_src1(#llvm_shl{src1=Src1}) -> Src1.
shl_src2(#llvm_shl{src2=Src2}) -> Src2.
shl_options(#llvm_shl{options=Options}) -> Options.

%%
%% lshr
%%
mk_lshr(Dst, Type, Src1, Src2, Options) ->
  #llvm_lshr{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
lshr_dst(#llvm_lshr{dst=Dst}) -> Dst.
lshr_type(#llvm_lshr{type=Type}) -> Type.
lshr_src1(#llvm_lshr{src1=Src1}) -> Src1.
lshr_src2(#llvm_lshr{src2=Src2}) -> Src2.
lshr_options(#llvm_lshr{options=Options}) -> Options.

%%
%% ashr
%%
mk_ashr(Dst, Type, Src1, Src2, Options) ->
  #llvm_ashr{dst=Dst, type=Type, src1=Src1, src2=Src2, options=Options}.
ashr_dst(#llvm_ashr{dst=Dst}) -> Dst.
ashr_type(#llvm_ashr{type=Type}) -> Type.
ashr_src1(#llvm_ashr{src1=Src1}) -> Src1.
ashr_src2(#llvm_ashr{src2=Src2}) -> Src2.
ashr_options(#llvm_ashr{options=Options}) -> Options.


%%
%% and
%%
mk_and(Dst, Type, Src1, Src2) ->
  #llvm_and{dst=Dst, type=Type, src1=Src1, src2=Src2}.
and_dst(#llvm_and{dst=Dst}) -> Dst.
and_type(#llvm_and{type=Type}) -> Type.
and_src1(#llvm_and{src1=Src1}) -> Src1.
and_src2(#llvm_and{src2=Src2}) -> Src2.

%%
%% or
%%
mk_or(Dst, Type, Src1, Src2) ->
  #llvm_or{dst=Dst, type=Type, src1=Src1, src2=Src2}.
or_dst(#llvm_or{dst=Dst}) -> Dst.
or_type(#llvm_or{type=Type}) -> Type.
or_src1(#llvm_or{src1=Src1}) -> Src1.
or_src2(#llvm_or{src2=Src2}) -> Src2.

%%
%% xor
%%
mk_xor(Dst, Type, Src1, Src2) ->
  #llvm_xor{dst=Dst, type=Type, src1=Src1, src2=Src2}.
xor_dst(#llvm_xor{dst=Dst}) -> Dst.
xor_type(#llvm_xor{type=Type}) -> Type.
xor_src1(#llvm_xor{src1=Src1}) -> Src1.
xor_src2(#llvm_xor{src2=Src2}) -> Src2.


mk_extractvalue(Dst, Type, Val, Idx, Idxs) ->
  #llvm_extractvalue{dst=Dst,type=Type,val=Val,idx=Idx,idxs=Idxs}.
extractvalue_dst(#llvm_extractvalue{dst=Dst})-> Dst.
extractvalue_type(#llvm_extractvalue{type=Type})-> Type.
extractvalue_val(#llvm_extractvalue{val=Val})-> Val.
extractvalue_idx(#llvm_extractvalue{idx=Idx})-> Idx.
extractvalue_idxs(#llvm_extractvalue{idxs=Idxs})-> Idxs.

mk_alloca(Dst, Type, Num, Align) ->
  #llvm_alloca{dst=Dst, type=Type, num=Num, align=Align}.
alloca_dst(#llvm_alloca{dst=Dst}) -> Dst.
alloca_type(#llvm_alloca{type=Type})-> Type.
alloca_num(#llvm_alloca{num=Num})-> Num.
alloca_align(#llvm_alloca{align=Align})-> Align.

mk_load(Dst, Type, Pointer, Alignment, Nontemporal, Volatile) ->
  #llvm_load{dst=Dst, type=Type, pointer=Pointer, alignment=Alignment,
    nontemporal=Nontemporal, volatile=Volatile}.
load_dst(#llvm_load{dst=Dst})-> Dst.
load_type(#llvm_load{type=Type})-> Type.
load_pointer(#llvm_load{pointer=Pointer})-> Pointer.
load_alignment(#llvm_load{alignment=Alignment})-> Alignment.
load_nontemporal(#llvm_load{nontemporal=Nontemporal})-> Nontemporal.
load_volatile(#llvm_load{volatile=Volatile})-> Volatile.

mk_store(Dst, Type, Pointer, Alignment, Nontemporal, Volatile) ->
  #llvm_store{dst=Dst, type=Type, pointer=Pointer, alignment=Alignment,
    nontemporal=Nontemporal, volatile=Volatile}.
store_dst(#llvm_store{dst=Dst})-> Dst.
store_type(#llvm_store{type=Type})-> Type.
store_pointer(#llvm_store{pointer=Pointer})-> Pointer.
store_alignment(#llvm_store{alignment=Alignment})-> Alignment.
store_nontemporal(#llvm_store{nontemporal=Nontemporal})-> Nontemporal.
store_volatile(#llvm_store{volatile=Volatile})-> Volatile.

mk_icmp(Dst, Cond, Type, Src1, Src2) ->
  #llvm_icmp{dst=Dst,'cond'=Cond,type=Type,src1=Src1,src2=Src2}.
icmp_dst(#llvm_icmp{dst=Dst}) -> Dst.
icmp_cond(#llvm_icmp{'cond'=Cond}) -> Cond.
icmp_type(#llvm_icmp{type=Type}) -> Type.
icmp_src1(#llvm_icmp{src1=Src1}) -> Src1.
icmp_src2(#llvm_icmp{src2=Src2}) -> Src2.

mk_fcmp(Dst, Cond, Type, Src1, Src2) ->
  #llvm_fcmp{dst=Dst,'cond'=Cond,type=Type,src1=Src1,src2=Src2}.
fcmp_dst(#llvm_fcmp{dst=Dst}) -> Dst.
fcmp_cond(#llvm_fcmp{'cond'=Cond}) -> Cond.
fcmp_type(#llvm_fcmp{type=Type}) -> Type.
fcmp_src1(#llvm_fcmp{src1=Src1}) -> Src1.
fcmp_src2(#llvm_fcmp{src2=Src2}) -> Src2.

mk_phi(Dst, Type, Value_label_list) ->
  #llvm_phi{dst=Dst, type=Type,value_label_list=Value_label_list}.
phi_dst(#llvm_phi{dst=Dst}) ->
  Dst.
phi_type(#llvm_phi{type=type}) ->
  type.
phi_value_label_list(#llvm_phi{value_label_list=Value_label_list}) ->
  Value_label_list.


pp_ins(Dev, I) ->
  io:format(Dev, "  ", []),
  case I of
    #llvm_ret{} ->
      io:format(Dev, "ret ~w ~w~n", [ret_type(I), ret_value(I)]);
    #llvm_br{} ->
      io:format(Dev, "br label %~w~n", [br_dst(I)]);
    #llvm_br_cond{} ->
      io:format(Dev, "br i1 ~w, label %~w, label %~w~n", 
        [br_cond_cond(I), br_cond_true_label(I), br_cond_false_label(I)]);
    #llvm_add{} ->
      io:format(Dev, "~w = add ", [add_dst(I)]),
      pp_options(Dev, add_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [add_type(I), add_src1(I), add_src2(I)]);
    #llvm_fadd{} ->
      io:format(Dev, "~w = fadd ", [fadd_dst(I)]),
      pp_options(Dev, fadd_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [fadd_type(I), fadd_src1(I), fadd_src2(I)]);
    #llvm_sub{} ->
      io:format(Dev, "~w = sub ", [sub_dst(I)]),
      pp_options(Dev, sub_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [sub_type(I), sub_src1(I), sub_src2(I)]);
    #llvm_fsub{} ->
      io:format(Dev, "~w = fsub ", [fsub_dst(I)]),
      pp_options(Dev, fsub_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [fsub_type(I), fsub_src1(I), fsub_src2(I)]);
    #llvm_mul{} ->
      io:format(Dev, "~w = mul ", [mul_dst(I)]),
      pp_options(Dev, mul_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [mul_type(I), mul_src1(I), mul_src2(I)]);
    #llvm_fmul{} ->
      io:format(Dev, "~w = fmul ", [fmul_dst(I)]),
      pp_options(Dev, fmul_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [fmul_type(I), fmul_src1(I), fmul_src2(I)]);
    #llvm_udiv{} ->
      io:format(Dev, "~w = udiv ", [udiv_dst(I)]),
      pp_options(Dev, udiv_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [udiv_type(I), udiv_src1(I), udiv_src2(I)]);
    #llvm_sdiv{} ->
      io:format(Dev, "~w = sdiv ", [sdiv_dst(I)]),
      pp_options(Dev, sdiv_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [sdiv_type(I), sdiv_src1(I), sdiv_src2(I)]);
    #llvm_fdiv{} ->
      io:format(Dev, "~w = fdiv ", [fdiv_dst(I)]),
      pp_options(Dev, fdiv_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [fdiv_type(I), fdiv_src1(I), fdiv_src2(I)]);
    #llvm_urem{} ->
      io:format(Dev, "~w = urem ", [urem_dst(I)]),
      pp_options(Dev, urem_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [urem_type(I), urem_src1(I), urem_src2(I)]);
    #llvm_srem{} ->
      io:format(Dev, "~w = srem ", [srem_dst(I)]),
      pp_options(Dev, srem_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [srem_type(I), srem_src1(I), srem_src2(I)]);
    #llvm_frem{} ->
      io:format(Dev, "~w = frem ", [frem_dst(I)]),
      pp_options(Dev, frem_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [frem_type(I), frem_src1(I), frem_src2(I)]);
    #llvm_shl{} ->
      io:format(Dev, "~w = shl ", [shl_dst(I)]),
      pp_options(Dev, shl_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [shl_type(I), shl_src1(I), shl_src2(I)]);
    #llvm_lshr{} ->
      io:format(Dev, "~w = lshr ", [lshr_dst(I)]),
      pp_options(Dev, lshr_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [lshr_type(I), lshr_src1(I), lshr_src2(I)]);
    #llvm_ashr{} ->
      io:format(Dev, "~w = ashr ", [ashr_dst(I)]),
      pp_options(Dev, ashr_options(I)),
      io:format(Dev, "~w ~w, ~w~n",
        [ashr_type(I), ashr_src1(I), ashr_src2(I)]);
    #llvm_and{} ->
      io:format(Dev, "~w = and ", [and_dst(I)]),
      io:format(Dev, "~w ~w, ~w~n",
        [and_type(I), and_src1(I), and_src2(I)]);
    #llvm_or{} ->
      io:format(Dev, "~w = or ", [or_dst(I)]),
      io:format(Dev, "~w ~w, ~w~n",
        [or_type(I), or_src1(I), or_src2(I)]);
    #llvm_xor{} ->
      io:format(Dev, "~w = xor ", [xor_dst(I)]),
      io:format(Dev, "~w ~w, ~w~n",
        [xor_type(I), xor_src1(I), xor_src2(I)]);
    #llvm_alloca{} ->
      io:format(Dev, "~w = alloca ~w ", [alloca_dst(I), alloca_type(I)]),
      case alloca_num(I) of
        [] -> ok;
        Num -> io:format(Dev, ",~w ~w ", [alloca_type(I), Num])
      end,
      case alloca_align(I) of
        [] ->ok;
        Align -> io:format(Dev, ",align ~w", [Align])
      end,
      io:format(Dev, "~n", []);
    #llvm_load{} ->
      io:format(Dev, "~w = ",[load_dst(I)]),
      case load_volatile(I) of
        true -> io:format(Dev, "volatile ", []);
        false -> ok
    end,
      io:format(Dev, "load ~w* ~w ", 
        [load_type(I), load_pointer(I)]),
      case load_alignment(I) of 
        [] -> ok;
        Al -> io:format(Dev, ", align ~w ", [Al])
      end,
      case load_nontemporal(I) of
        [] -> ok;
        In -> io:format(Dev, ", !nontemporal !~w", [In])
      end,
      io:format(Dev, "~n", []);
    #llvm_store{} ->
      io:format(Dev, "~w = ",[store_dst(I)]),
      case store_volatile(I) of
        true -> io:format(Dev, "volatile ", []);
        false -> ok
    end,
      io:format(Dev, "store ~w* ~w ", 
        [store_type(I), store_pointer(I)]),
      case store_alignment(I) of 
        [] -> ok;
        Al -> io:format(Dev, ", align ~w ", [Al])
      end,
      case store_nontemporal(I) of
        [] -> ok;
        In -> io:format(Dev, ", !nontemporal !~w", [In])
      end,
      io:format(Dev, "~n", []);
    #llvm_icmp{} ->
      io:format(Dev, "~w = icmp ~w ~w ~w, ~w~n",
        [icmp_dst(I), icmp_cond(I), icmp_type(I), icmp_src1(I), icmp_src2(I)]);
    #llvm_fcmp{} ->
      io:format(Dev, "~w = fcmp ~w ~w ~w, ~w~n",
        [fcmp_dst(I), fcmp_cond(I), fcmp_type(I), fcmp_src1(I), fcmp_src2(I)]);
    #llvm_phi{} ->
      io:format(Dev, "~w = phi ~w ", [phi_dst(I), phi_type(I)]),
      pp_phi_value_labels(Dev, I),
      io:format(Dev, "~n", []);

      Other -> exit({?MODULE, pp_ins, {"Unknown LLVM instruction", Other}})
    end.

  pp_options(_Dev, []) -> ok;
  pp_options(Dev, [O|Os])-> io:format(Dev,"~w ", [erlang:atom_to_list(O)]),
    pp_options(Dev, Os).

  pp_phi_value_labels(_Dev, []) -> ok;
  pp_phi_value_labels(Dev, { Value, Label}) ->
    io:format(Dev, "[ ~w, ~w ]", [Value, Label]);
  pp_phi_value_labels(Dev,[{Value,Label}| VL]) ->
    io:format(Dev, "[ ~w, ~w ], ", [Value, Label]),
    pp_phi_value_labels(Dev, VL).
