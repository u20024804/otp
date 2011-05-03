%% -*- erlang-indent-level: 2 -*-


-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").
-include("hipe_llvm.hrl").

-export([translate/1]).

-define(HP, "%hp_var").

translate(RTL) ->
  hipe_gensym:init(llvm),
  % Data = hipe_rtl:rtl_data(RTL),
  Code = hipe_rtl:rtl_code(RTL),
  Fun =  hipe_rtl:rtl_fun(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  % To be used later
  _IsClosure = hipe_rtl:rtl_is_closure(RTL),
  _IsLeaf = hipe_rtl:rtl_is_leaf(RTL),
  io:format("Geia sou llvm!~n"),
  {_, Fun_Name, _} = Fun,

  {ok, File_rtl} = file:open(atom_to_list(Fun_Name) ++ ".rtl", [write]),
  hipe_rtl:pp(File_rtl, RTL),
  file:close(File_rtl),

  {ok, File_llvm} = file:open(atom_to_list(Fun_Name) ++ ".ll", [write]),
  Llvm_Code = translate_instr_list(Code, []),
  Final_Code = create_header(Fun, Params, Llvm_Code),
  hipe_llvm:pp_ins(File_llvm, Final_Code),
  create_main(File_llvm, Fun, Params),
  file:close(File_llvm).

%%-----------------------------------------------------------------------------

translate_instr_list([], Acc) -> 
  lists:reverse(lists:flatten(Acc));
translate_instr_list([I|Is], Acc) ->
  Acc1 = translate_instr(I),
  translate_instr_list(Is, [Acc1|Acc]).


translate_instr(I) ->
  case I of
    #alu{} -> trans_alu(I);
    #alub{} -> trans_alub(I);
    #branch{} -> trans_branch(I);
    #call{} -> trans_call(I);
    #comment{} -> trans_comment(I);
    %#enter{} -> ok;
    %#fconv{} -> ok;
    #fixnumop{} -> trans_fixnum(I);
    %#fload{} -> ok;
    %#fmove{} -> ok;
    %#fp{} -> ok;
    %#fp_unop{} -> ok;
    %#fstore{} -> ok;
    #gctest{} -> trans_gctest(I);
    #goto{} -> trans_goto(I);
    %#goto_index{} -> ok;
    #label{} -> trans_label(I);
    %#load{} -> ok;
    %#load_address{} -> ok;
    %#load_atom{} -> ok;
    %#load_word_index{} -> ok;
    %#move{} -> trans_move(I);
    %#multimove{} -> ok;
    #phi{} -> trans_phi(I);
    #return{} -> trans_return(I);
    #store{} -> trans_store(I);
    %#switch{} -> ok;
    Other -> 
      exit({?MODULE, translate_instr, {"unknown RTL instruction", Other}})
  end.

%%-----------------------------------------------------------------------------


isPrecoloured(X) -> hipe_rtl_arch:is_precoloured(X).
%%
%% alu
%% 
trans_alu(I) ->
  % Destination is a register and not in SSA Form..
  _Dst = hipe_rtl:alu_dst(I),
  _Src1 = hipe_rtl:alu_src1(I),
  _Src2 = hipe_rtl:alu_src2(I),
  Dst = case isPrecoloured(_Dst) of
    true -> mk_temp();
    false -> trans_dst(hipe_rtl:alu_dst(I))
  end,
  {Src1, I1} = 
  case isPrecoloured(_Src1) of
    true -> 
      T1 = mk_temp(),
      {T1, hipe_llvm:mk_load(T1, "i64", trans_src(_Src1), [], [], false)};
    false ->
      {trans_src(_Src1), []}
  end,
  {Src2, I2} = 
  case isPrecoloured(_Src2) of
    true -> 
      T2 = mk_temp(),
      {T2, hipe_llvm:mk_load(T2, "i64", trans_src(_Src2), [], [], false)};
    false ->
      {trans_src(_Src2), []}
  end,
  Type = arg_type(hipe_rtl:alu_src1(I)),
  Op =  trans_op(hipe_rtl:alu_op(I)),
  I3 = hipe_llvm:mk_operation(Dst, Op, Type, Src1, Src2, []),
  I4 = case isPrecoloured(_Dst) of 
    true -> 
      Dst2 = trans_dst(hipe_rtl:alu_dst(I)),
      hipe_llvm:mk_store(Type, Dst, Type, Dst2, [], [], false);
    false -> []
  end,
  [I4, I3, I2, I1].
          
%%
%% alub
%%
trans_alub(I) ->
  case hipe_rtl:alub_cond(I) of
    overflow -> trans_alub_overflow(I);
    not_overflow -> trans_alub_overflow(I);
    _ -> trans_alub_no_overflow(I)
  end.

trans_alub_overflow(I) ->
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  Src1 =  trans_src(hipe_rtl:alub_src1(I)),
  Src2 =  trans_src(hipe_rtl:alub_src2(I)),
  %TODO: Fix call
  I1 = hipe_llvm:mk_call(T1, false, [], [], "{i64, i1}",
    "@llvm.sadd.with.overflow.i64", [{"i64", Src1},{"i64", Src2}], []),
  %
  Dst = trans_dst(hipe_rtl:alub_dst(I)),
  I2 = hipe_llvm:mk_extractvalue(Dst, "{i64, i1}", T1 , "0", []),
  T2 = mk_temp(),
  I3 = hipe_llvm:mk_extractvalue(T2, "{i64, i1}", T1, "1", []),
  True_label = mk_jump_label(hipe_rtl:alub_false_label(I)),
  False_label = mk_jump_label(hipe_rtl:alub_true_label(I)),
  I4 = hipe_llvm:mk_br_cond(T2, True_label, False_label),
  [I4, I3, I2, I1].

trans_alub_no_overflow(I) ->
  %alu
  T = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
    hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  I1 = trans_alu(T),
  %icmp
  Type = arg_type(hipe_rtl:alub_src1(I)),
  Src1 = trans_src(hipe_rtl:alub_src1(I)),
  Src2 = trans_src(hipe_rtl:alub_src2(I)),
  Cond = hipe_rtl:alub_cond(I),
  T1 = mk_temp(),
  I2 = hipe_llvm:mk_icmp(T1, Cond, Type, Src1, Src2),
  %br
  True_label = mk_jump_label(hipe_rtl:alub_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:alub_false_label(I)),
  I3 = hipe_llvm:mk_br_cond(T1, True_label, False_label),
  [I3, I2, I1].

%%
%% branch
%%
trans_branch(I) ->
  Type = arg_type(hipe_rtl:branch_src1(I)),
  Src1 = trans_src(hipe_rtl:branch_src1(I)),
  Src2 = trans_src(hipe_rtl:branch_src2(I)),
  Cond = hipe_rtl:branch_cond(I),
  %icmp
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  I1 = hipe_llvm:mk_icmp(T1, Cond, Type, Src1, Src2),
  %br
  True_label = mk_jump_label(hipe_rtl:branch_true_label(I)),
  False_label = mk_jump_label(hipe_rtl:branch_false_label(I)),
  I2 = hipe_llvm:mk_br_cond(T1, True_label, False_label),
  [I2, I1].

%%
%% call
%%
trans_call(I) ->
  I1 = case hipe_rtl:call_fun(I) of
    Prim when is_atom(Prim) ->
      trans_prim_call(I);
    {M,F,A} when is_atom(M), is_atom(F), is_integer(A) ->
      trans_mfa_call(I)
  end,
  I2 = case hipe_rtl:call_continuation(I) of
    [] -> [];
    CC -> trans_goto(hipe_rtl:mk_goto(CC))
  end,
  [I2, I1].

trans_prim_call(I) ->
  [Dst|_Dsts] = hipe_rtl:call_dstlist(I),
  [Src1|[Src2|_Args]] =  hipe_rtl:call_arglist(I),
  Op = trans_prim_op(hipe_rtl:call_fun(I)),
  T1 = hipe_rtl:mk_alu(Dst, Src1, Op, Src2), 
  I1 = trans_alu(T1),
  I1.

trans_mfa_call(I) ->
  exit({?MODULE, trans_mfa_call, I}).

%%
%% trans_comment
%%
trans_comment(I) ->
  I1 = hipe_llvm:mk_comment(hipe_rtl:comment_text(I)),
  I1.

%%
%% fixnumop
%%
trans_fixnum(I) ->
  Dst = hipe_rtl:fixnumop_dst(I),
  Src = hipe_rtl:fixnumop_src(I),
  I1 = case hipe_rtl:fixnumop_type(I) of
    tag ->
      trans_alu(hipe_tagscheme:realtag_fixnum(Dst, Src));
    untag ->
      trans_alu(hipe_tagscheme:realuntag_fixnum(Dst, Src))
  end,
  I1.

%%
%% gctest
%%
trans_gctest(I) ->
  % For now ignore gc_test. Just print it as comment
  W = trans_src(hipe_rtl:gctest_words(I)),
  I1 = hipe_llvm:mk_comment("gc_test("++W++")"),
  I1.

%%
%% goto
%%
trans_goto(I) ->
  I1 = hipe_llvm:mk_br(mk_jump_label(hipe_rtl:goto_label(I))),
  I1.

%%
%% label
%%
trans_label(I) ->
  Label  = mk_label(hipe_rtl:label_name(I)),
  I1 = hipe_llvm:mk_label(Label),
  I1.

%%
%% move
%%
%trans_move(I) ->
%  Dst = hipe_rtl:move_dst(I),
%  Src = hipe_rtl:move_src(I),
%  Src_type = arg_type(Src),
%  %% %src_addr = alloca i32
%  io:format(Dev, "  ", []),
%  trans_arg(Dev, Src, dst),
%  io:format(Dev, "_addr ", []),
%  io:format(Dev, " = ", []),
%  io:format(Dev, "alloca ~w~n", [Src_type]),
%  %% store i32 src, i32* src_addr
%  io:format(Dev, "  ", []),
%  io:format(Dev, "store ", []),
%  trans_arg(Dev, Src),
%  io:format(Dev, ", ~w* ", [Src_type]),
%  trans_arg(Dev, Src, dst),
%  io:format(Dev, "_addr ~n", []),
%  %% dst = load i32* src_addr
%  io:format(Dev, "  ", []),
%  trans_arg(Dev, Dst, dst),
%  io:format(Dev, " = ", []),
%  io:format(Dev, "load ~w* ", [Src_type]),
%  trans_arg(Dev, Src, dst),
%  io:format(Dev, "_addr~n", []).

%% 
%% phi
%%
trans_phi(I) ->
  Dst = hipe_rtl:phi_dst(I),
  I1 = hipe_llvm:mk_phi(trans_dst(Dst) , arg_type(Dst), 
    trans_phi_list(hipe_rtl:phi_arglist(I))),
  I1.

trans_phi_list([]) -> [];
trans_phi_list([{Label, Value}| Args]) ->
  [{trans_src(Value), mk_jump_label(Label)} | trans_phi_list(Args)].

%%
%% return 
%%
%% TODO: Take care of returning many items
trans_return(I) ->
  [A | _As] = hipe_rtl:return_varlist(I),
  FixedRegs = fixed_registers(),
  RetFixedRegs =  lists:map(fun(X) -> "%"++X++"_ret" end, FixedRegs),
  I1 = lists:map(fun (X) -> hipe_llvm:mk_load("%"++X++"_ret", "i64",
          "%"++X++"_var",[],[],false) end, FixedRegs),
  Ret1 = {arg_type(A), trans_src(A)},
  Ret2 = lists:map(fun(X) -> {"i64", X} end, RetFixedRegs),
  I2 = hipe_llvm:mk_ret([Ret1|Ret2]),
  [I2, I1].



%%
%% store 
%%
trans_store(I) ->
  Base = hipe_rtl:store_base(I),
  I1 = case hipe_rtl_arch:is_precoloured(Base) of
    true -> trans_store_reg(I);
    false -> exit({?MODULE, trans_store ,{"Non Implemened yet", false}})
  end,
  I1.

trans_store_reg(I) ->
  B = hipe_rtl:store_base(I),
  Base  = trans_reg(B),
  D1 = mk_hp(),
  I1 = hipe_llvm:mk_load(D1, "i64", Base, [],  [], false),
  D2 = mk_hp(),
  I2 = hipe_llvm:mk_inttoptr(D2, "i64", D1, "i64"),
  Offset = trans_src(hipe_rtl:store_offset(I)), 
  D3 = mk_hp(),
  I3 = hipe_llvm:mk_getelementptr(D3, "i64", D2, [{"i64", Offset}], false),
  Value = hipe_rtl:store_src(I),
  I4 = hipe_llvm:mk_store("i64", trans_src(Value), "i64", D3, [], [],
                          false),
  [I4, I3, I2, I1].

%%-----------------------------------------------------------------------------


mk_label(N) ->
  "L" ++ integer_to_list(N).

mk_jump_label(N) ->
  "%L" ++ integer_to_list(N).

mk_temp() ->
  "%t" ++ integer_to_list(hipe_gensym:new_var(llvm)).
mk_temp(N) ->
  "%t" ++ integer_to_list(N).

mk_hp() ->
  "%hp_var_" ++ integer_to_list(hipe_gensym:new_var(llvm)).
mk_hp(N) ->
  "%hp_var_" ++ integer_to_list(N).

%% Translate source and destination arguments
trans_src(A) ->
  case hipe_rtl:is_imm(A) of
    true ->  integer_to_list(hipe_rtl:imm_value(A));
    false -> trans_dst(A)  
  end.

trans_dst(A) ->
  case hipe_rtl:is_var(A) of
    true ->
      "%v" ++ integer_to_list(hipe_rtl:var_index(A));
    false ->
      case hipe_rtl:is_reg(A) of
        true ->
          trans_reg(A);
        false ->
          exit({?MODULE, trans_dst, {"bad RTL arg",A}})
      end
  end.

%% Translate register. If it is precoloured it must be mapped to some llvm var
%% that corresponds to an argument
trans_reg(Arg) ->
  Index = hipe_rtl:reg_index(Arg),
  case hipe_rtl_arch:is_precoloured(Arg) of
    true -> map_precoloured_reg(Index);
    false -> hipe_rtl_arch:reg_name(Index)
  end.

map_precoloured_reg(Index) ->
  %TODO : Works only for amd64 architecture and only for register r15
  case hipe_rtl_arch:reg_name(Index) of
    "%r15" -> "%hp_var";
    _ ->  exit({?MODULE, map_precoloured_reg, {"Register not mapped yet",
            Index}})
  end.

trans_op(Op) ->
  case Op of
    add -> add;
    sub -> sub;
    'or' -> 'or';
    'and' -> 'and';
    'xor' -> 'xor';
    sll -> shl;
    srl -> lshr;
    sra -> ashr;
    mul -> mul;
    'fdiv' -> fdiv;
    'sdiv' -> sdiv;
    'srem' -> srem;
    Other -> exit({?MODULE, trans_op, {"Unknown RTL Operator",Other}})
  end.

trans_prim_op(Op) -> 
  case Op of
    '+' -> add;
    '-' -> sub;
    '*' -> mul;
    'div' -> 'sdiv';
    '/' -> 'fdiv';
    'rem' -> 'srem';
    Other -> exit({?MODULE, trans_prim_op, {"unknown prim op", Other}})
  end.

%% Return the type of arg A (only integers of 32 bits supported).
arg_type(A) ->
  case hipe_rtl:is_var(A) of
    true -> "i64";
    false ->
      case hipe_rtl:is_reg(A) of
        true -> "i64";
        false -> "i64"
      end
  end.

%%-----------------------------------------------------------------------------

%% Create Header for Function 

create_header(Name, Params, Code) ->
  % TODO: What if arguments more than available registers?
  % TODO: Jump to correct label
  {_,N,_} = Name,

  Fixed_regs = fixed_registers(),
  Args1 = header_regs(Fixed_regs, []),
  Args2 = lists:map( fun(X) -> {"i64", "%v" ++
          integer_to_list(hipe_rtl:var_index(X))}
    end, Params),
  
  I1 = hipe_llvm:mk_label("Entry"),
  I2 = load_regs(Fixed_regs),
  I3 = hipe_llvm:mk_br(mk_jump_label(1)),
  Final_Code = lists:flatten([I1,I2,I3])++Code,
  [_|[_|Typ]] = lists:foldl(fun(X,Y) -> Y++", i64" end, [],
    Fixed_regs++Params) ,
  Type = "{"++Typ++"}",
  hipe_llvm:mk_fun_def([], [], "cc 11", [], Type, atom_to_list(N),
                        Args1++Args2, [], [], Final_Code).

fixed_registers() ->
  case get(hipe_target_arch) of
    x86 -> ["hp", "p", "nsp"];
    amd64 ->
      ["hp", "p", "nsp", "fcalls", "heap_limit"];
    Other ->
      exit({?MODULE, map_registers, {"Unknown Architecture"}})
  end.

header_regs(Regs) -> header_regs(Regs, []).

header_regs([], Acc) -> Acc;
header_regs([R|Rs], Acc) ->
  Reg = {"i64",  "%"++R++"_in"},
  header_regs(Rs, [Reg|Acc]).

load_regs(Regs) -> load_regs(Regs, []).

load_regs([], Acc) -> Acc;
load_regs([R | Rs], Acc) ->
  I1 = hipe_llvm:mk_alloca("%"++R++"_var", "i64", [], []),
  I2 = hipe_llvm:mk_store("i64", "%"++R++"_in", "i64", "%"++R++"_var", [], [], false),
  load_regs(Rs, [I1,I2,Acc]).


%%-----------------------------------------------------------------------------
%%
%% Only For Testing
%%


%% Create Main Function (Only for testing reasons)

create_main(Dev, Name, Params) ->
  {_,N,_} = Name,
%  io:format(Dev, "@.str = private constant [3 x i8] c\"%d\\00\", align 1;",[]),
%  io:format(Dev, "~n~ndefine i64 @main() {~n", []),
%  io:format(Dev, "Entry:~n", []),
%  T1 = mk_temp(hipe_gensym:new_var(llvm)),
%  io:format(Dev, "~s = call {i64,i64,i64,i64,i64,i64} @~w(", [T1, N]),
%  init_params(Dev, 5+erlang:length(Params)),
%  io:format(Dev, ")~n", []),
%
%  io:format(Dev, "%0 = tail call i64 (i8*, ...)* @printf(i8* noalias " ++ 
%    "getelementptr inbounds ([3 x i8]* @.str, i64 0, i64 0)," ++ 
%    " i64 ~s) nounwind~n", [T1]),
%  io:format(Dev, "ret i64 ~s~n}~n",[T1]),
%  io:format(Dev, "declare i64 @printf(i8* noalias, ...) nounwind~n",[]),
  io:format(Dev, "declare {i64, i1} @llvm.sadd.with.overflow.i64(i64 %a, "++
    "i64%b)~n", []).

%% Print random parameters in main function
init_params(Dev, 1) -> 
  io:format(Dev,"i64 ~w",[random:uniform(20)]);
init_params(Dev, N) -> 
  io:format(Dev,"i64 ~w,",[random:uniform(20)]),
  init_params(Dev, N-1).
