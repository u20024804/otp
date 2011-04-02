%% -*- erlang-indent-level: 2 -*-

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").

-export([translate/1]).

translate(RTL) ->
  hipe_gensym:init(llvm),
  % Data = hipe_rtl:rtl_data(RTL),
  Code = hipe_rtl:rtl_code(RTL),
  Fun =  hipe_rtl:rtl_fun(RTL),
  Params = hipe_rtl:rtl_params(RTL),
  io:format("Geia sou llvm!~n"),
  {_, Fun_Name, _} = Fun,

  {ok, File_rtl} = file:open(atom_to_list(Fun_Name) ++ ".rtl", [write]),
  hipe_rtl:pp(File_rtl, RTL),
  file:close(File_rtl),

  {ok, File_llvm} = file:open(atom_to_list(Fun_Name) ++ ".ll", [write]),
  create_header(File_llvm, Fun, Params),
  translate_instrs(File_llvm, Code),
  create_main(File_llvm, Fun, Params),
  file:close(File_llvm).

%%-----------------------------------------------------------------------------

translate_instrs(Dev, []) -> 
  io:format(Dev,"~n}~n",[]),
  ok;
translate_instrs(Dev, [I|Is]) ->
  translate_instr(Dev, I),
  translate_instrs(Dev, Is).


translate_instr(Dev, I) ->
  case I of
    #alu{} -> trans_alu(Dev, I);
    #alub{} -> trans_alub(Dev, I);
    #branch{} -> trans_branch(Dev, I);
    #call{} -> trans_call(Dev, I);
    #comment{} -> trans_comment(Dev, I);
    %#enter{} -> ok;
    %#fconv{} -> ok;
    #fixnumop{} -> trans_fixnum(Dev, I);
    %#fload{} -> ok;
    %#fmove{} -> ok;
    %#fp{} -> ok;
    %#fp_unop{} -> ok;
    %#fstore{} -> ok;
    #gctest{} -> trans_gctest(Dev, I);
    #goto{} -> trans_goto(Dev, I);
    %#goto_index{} -> ok;
    #label{} -> trans_label(Dev, I);
    %#load{} -> ok;
    %#load_address{} -> ok;
    %#load_atom{} -> ok;
    %#load_word_index{} -> ok;
    %#move{} -> trans_move(Dev, I);
    %#multimove{} -> ok;
    #phi{} -> trans_phi(Dev, I);
    #return{} -> trans_return(Dev, I);
    #store{} -> ok;
    %#switch{} -> ok;
    Other -> 
      exit({?MODULE, translate_instr, {"unknown RTL instruction", Other}})
  end.

%%-----------------------------------------------------------------------------


%%
%% alu
%% 
trans_alu(Dev, I) ->
  Dst = arg_to_var(hipe_rtl:alu_dst(I)),
  Src1 = arg_to_var(hipe_rtl:alu_src1(I)),
  Src2 = arg_to_var(hipe_rtl:alu_src2(I)),
  Type = arg_type(hipe_rtl:alu_src1(I)),
  I1 = case hipe_rtl:alu_op(I) of
    add -> hipe_llvm:mk_add(Dst, Type, Src1, Src2, []);
    sub -> hipe_llvm:mk_sub(Dst, Type, Src1, Src2, []);
    'or' -> hipe_llvm:mk_or(Dst, Type, Src1, Src2, []);
    'and' -> hipe_llvm:mk_and(Dst, Type, Src1, Src2);
    'xor' -> hipe_llvm:mk_xor(Dst, Type, Src1, Src2);
    sll -> hipe_llvm:mk_shl(Dst, Type, Src1, Src2, []);
    srl -> hipe_llvm:mk_lshr(Dst, Type, Src1, Src2, []);
    sra -> hipe_llvm:mk_ashr(Dst, Type, Src1, Src2, []);
    %TODO: Following cases should be removed when call is fixed
    mul -> hipe_llvm:mk_mul(Dst, Type, Src1, Src2, []);
    'fdiv' -> hipe_llvm:mk_fdiv(Dst, Type, Src1, Src2, []);
    'sdiv' -> hipe_llvm:mk_sdiv(Dst, Type, Src1, Src2, []);
    'srem' -> hipe_llvm:mk_srem(Dst, Type, Src1, Src2, []);
    Other -> exit({?MODULE, trans_alu,{"unknown ALU op", Other}})
  end,
  hipe_llvm:pp_ins(Dev, I1).

%%
%% alub
%%
trans_alub(Dev, I) ->
  case hipe_rtl:alub_cond(I) of
    overflow -> trans_alub_overflow(Dev, I);
    not_overflow -> trans_alub_overflow(Dev, I);
    _ -> trans_alub_no_overflow(Dev, I)
  end.


trans_alub_overflow(Dev, I) ->
  io:format(Dev, "  ", []),
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  io:format(Dev, "~s = ", [T1]),
  io:format(Dev, "call {i32, i1} @llvm.sadd.with.overflow.i32(", []),
  trans_arg(Dev, hipe_rtl:alub_src1(I)),
  io:format(Dev, ", ", []),
  trans_arg(Dev, hipe_rtl:alub_src2(I)),
  io:format(Dev, ")~n", []),
  Dst = arg_to_var(hipe_rtl:alub_dst(I)),
  I2 = hipe_llvm:mk_extractvalue(Dst, "{i32, i1}", T1 , "0", []),
  hipe_llvm:pp_ins(Dev, I2),
  T2 = mk_temp(hipe_gensym:new_var(llvm)),
  I3 = hipe_llvm:mk_extractvalue(T2, "{i32, i1}", T1, "1", []),
  hipe_llvm:pp_ins(Dev, I3),
  True_label = mk_label(hipe_rtl:alub_true_label(I)),
  False_label = mk_label(hipe_rtl:alub_false_label(I)),
  I4 = hipe_llvm:mk_br_cond(T2, True_label, False_label),
  hipe_llvm:pp_ins(Dev, I4).

trans_alub_no_overflow(Dev, I) ->
  %alu
  I1 = hipe_rtl:mk_alu(hipe_rtl:alub_dst(I), hipe_rtl:alub_src1(I),
    hipe_rtl:alub_op(I), hipe_rtl:alub_src2(I)),
  trans_alu(Dev, I1),
  %icmp
  Type = arg_type(hipe_rtl:alub_src1(I)),
  Src1 = arg_to_var(hipe_rtl:alub_src1(I)),
  Src2 = arg_to_var(hipe_rtl:alub_src2(I)),
  Cond = hipe_rtl:alub_cond(I),
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  I2 = hipe_llvm:mk_icmp(T1, Cond, Type, Src1, Src2),
  hipe_llvm:pp_ins(Dev, I2),
  %br
  True_label = mk_label(hipe_rtl:alub_true_label(I)),
  False_label = mk_label(hipe_rtl:alub_false_label(I)),
  I3 = hipe_llvm:mk_br_cond(T1, True_label, False_label),
  hipe_llvm:pp_ins(Dev, I3).

%%
%% branch
%%
trans_branch(Dev, I) ->
  Type = arg_type(hipe_rtl:branch_src1(I)),
  Src1 = arg_to_var(hipe_rtl:branch_src1(I)),
  Src2 = arg_to_var(hipe_rtl:branch_src2(I)),
  Cond = hipe_rtl:branch_cond(I),
  %icmp
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  I1 = hipe_llvm:mk_icmp(T1, Cond, Type, Src1, Src2),
  hipe_llvm:pp_ins(Dev, I1),
  %br
  True_label = mk_label(hipe_rtl:branch_true_label(I)),
  False_label = mk_label(hipe_rtl:branch_false_label(I)),
  I2 = hipe_llvm:mk_br_cond(T1, True_label, False_label),
  hipe_llvm:pp_ins(Dev, I2).

%%
%% call
%%
trans_call(Dev, I) ->
  [Dst|_Dsts] = hipe_rtl:call_dstlist(I),
  Op = case hipe_rtl:call_fun(I) of
    '+' -> add;
    '-' -> sub;
    '*' -> mul;
    'div' -> 'sdiv';
    '/' -> 'fdiv';
    'rem' -> 'srem';
    Other -> exit({?MODULE, trans_call, {"unknown call", Other}})
  end,
  [Src1|[Src2|_Args]] =  hipe_rtl:call_arglist(I),
  I1 = hipe_rtl:mk_alu(Dst, Src1, Op, Src2), 
  trans_alu(Dev, I1),
  case hipe_rtl:call_continuation(I) of
    [] -> true;
    CC -> trans_goto(Dev, hipe_rtl:mk_goto(CC))
  end.

%%
%% trans_comment
%%
trans_comment(Dev, I) ->
  hipe_llvm:pp_ins(Dev, hipe_rtl:comment_text(I)).

%%
%% fixnumop
%%
trans_fixnum(Dev, I) ->
  Dst = hipe_rtl:fixnumop_dst(I),
  Src = hipe_rtl:fixnumop_src(I),
  case hipe_rtl:fixnumop_type(I) of
    tag ->
      trans_alu(Dev, hipe_tagscheme:realtag_fixnum(Dst, Src));
    untag ->
      trans_alu(Dev, hipe_tagscheme:realuntag_fixnum(Dst, Src))
  end.

%%
%% gctest
%%
trans_gctest(Dev, I) ->
  Words = integer_to_list(hipe_rtl:gctest_words(I)),
  hipe_llvm:pp_ins(Dev,
    hipe_llvm:mk_comment("gc_test"++Words)).

%%
%% goto
%%
trans_goto(Dev, I) ->
  hipe_llvm:pp_ins(Dev, hipe_llvm:mk_br("L"++
      integer_to_list(hipe_rtl:goto_label(I)))).

%%
%% label
%%
trans_label(Dev, I) ->
  io:format(Dev, "~nL~w:~n", [hipe_rtl:label_name(I)]).

%%
%% move
%%
%trans_move(Dev, I) ->
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
trans_phi(Dev, I) ->
  Dst = hipe_rtl:phi_dst(I),
  L = hipe_llvm:mk_phi(arg_to_var(Dst) , arg_type(Dst), 
    trans_phi_list(hipe_rtl:phi_arglist(I))),
  hipe_llvm:pp_ins(Dev, L).

%%
%% return 
%%
trans_return(Dev, I) ->
  [A | _As] = hipe_rtl:return_varlist(I),
  L = hipe_llvm:mk_ret( arg_type(A), arg_to_var(A)),
  hipe_llvm:pp_ins(Dev, L).


%%-----------------------------------------------------------------------------

mk_label(N) ->
  "L" ++ integer_to_list(N).

mk_temp(N) ->
  "%t" ++ integer_to_list(N).

arg_to_var(A) ->
  case hipe_rtl:is_var(A) of
    true ->
      "%v" ++ integer_to_list(hipe_rtl:var_index(A));
    false ->
      case hipe_rtl:is_reg(A) of
        true ->
          "%r"++integer_to_list(hipe_rtl:reg_index(A));
        false ->
          case hipe_rtl:is_imm(A) of
            true ->
              integer_to_list(hipe_rtl:imm_value(A));
            false ->
              case hipe_rtl:is_fpreg(A) of
                true ->
                  "%f"++integer_to_list(hipe_rtl:fpreg_index(A));
                false ->
                  case hipe_rtl:is_const_label(A) of
                    true->
                      "%DL"++integer_to_list(hipe_rtl:const_label_label(A));
                    false ->
                      case hipe_rtl:is_label(A) of
                        true ->
                          "L"++integer_to_list(hipe_rtl:label_name(A));
                        false->
                          exit({?MODULE,arg_to_var,{"bad RTL arg",A}})
                      end
                  end
              end
          end
      end
  end.

%trans_op(Op) ->
%  case Op of
%    add -> "add";
%    sub -> "sub";
%    'or'-> "or";
%    'and' -> "and";
%    'xor' -> "xor";
%    sll -> "shl";
%    srl -> "lshr";
%    sra -> "ashr";
%    Other -> exit({?MODULE, trans_alu,{"unknown ALU op", Other}})
%  end.

%% 
%% Pretty print arg(s).
%%
trans_args(Dev, A) ->
  trans_args(Dev, A, src).
%%
trans_args(_, [], _) ->
  ok;
trans_args(Dev, [A], Type) ->
  trans_arg(Dev, A, Type);
trans_args(Dev, [A|As], Type) ->
  trans_arg(Dev, A, Type),
  io:format(Dev, ", ", []),
  trans_args(Dev, As, Type).


trans_arg(Dev, A) ->
  trans_arg(Dev, A, src).
%%
trans_arg(Dev, A, Type) ->
  case Type of 
    src -> io:format(Dev, "~s ", [arg_type(A)]);
    dst -> ok
  end,
  case hipe_rtl:is_var(A) of
    true ->
      io:format(Dev, "%", []),
      hipe_rtl:pp_var(Dev, A);
    false ->
      case hipe_rtl:is_reg(A) of
        true ->
          io:format(Dev, "%", []),
          hipe_rtl:pp_reg(Dev, A);
        false ->
          case hipe_rtl:is_imm(A) of
            true ->
              Val = hipe_rtl:imm_value(A),
              io:format(Dev, "~w", [Val]);
            false ->
              case hipe_rtl:is_fpreg(A) of
                true ->
                  io:format(Dev, "f~w", [hipe_rtl:fpreg_index(A)]);
                false ->
                  ok
              end
          end
      end
  end.

trans_phi_list([]) -> [];
trans_phi_list([{Label, Value}| Args]) ->
  [{arg_to_var(Value), "%L"++integer_to_list(Label)}|trans_phi_list(Args)].

%% Return the type of arg A (only integers of 32 bits supported).
arg_type(A) ->
  case hipe_rtl:is_var(A) of
    true -> "i32";
    false ->
      case hipe_rtl:is_reg(A) of
        true -> "i32";
        false -> "i32"
      end
  end.

%%-----------------------------------------------------------------------------

%% Create Header for Function 

create_header(Dev, Name, Params) ->
  {_,N,_} = Name,
  io:format(Dev, "~n~ndefine i32 @~w(", [N]),
  trans_args(Dev, Params),
  io:format(Dev, ") {~n",[]).


%%-----------------------------------------------------------------------------
%%
%% Only For Testing
%%


%% Create Main Function (Only for testing reasons)

create_main(Dev, Name, Params) ->
  {_,N,_} = Name,
  io:format(Dev, "@.str = private constant [3 x i8] c\"%d\\00\", align 1;",[]),
  io:format(Dev, "~n~ndefine i32 @main() {~n", []),
  io:format(Dev, "Entry:~n", []),
  T1 = mk_temp(hipe_gensym:new_var(llvm)),
  io:format(Dev, "~s = call i32 @~w(", [T1, N]),
  init_params(Dev, erlang:length(Params)),
  io:format(Dev, ")~n", []),

  io:format(Dev, "%0 = tail call i32 (i8*, ...)* @printf(i8* noalias " ++ 
    "getelementptr inbounds ([3 x i8]* @.str, i64 0, i64 0)," ++ 
    " i32 ~s) nounwind~n", [T1]),
  io:format(Dev, "ret i32 ~s~n}~n",[T1]),
  io:format(Dev, "declare i32 @printf(i8* noalias, ...) nounwind~n",[]),
  io:format(Dev, "declare {i32, i1} @llvm.sadd.with.overflow.i32(i32 %a, "++
    "i32%b)~n", []).

%% Print random parameters in main function
init_params(Dev, 1) -> 
  io:format(Dev,"i32 ~w",[random:uniform(20)]);
init_params(Dev, N) -> 
  io:format(Dev,"i32 ~w,",[random:uniform(20)]),
  init_params(Dev, N-1).
