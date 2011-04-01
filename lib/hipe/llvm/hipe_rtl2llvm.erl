%% -*- erlang-indent-level: 2 -*-

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").

-export([translate/1]).

translate(RTL) ->
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
    #move{} -> trans_move(Dev, I);
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
  io:format(Dev,"  ", []),
  trans_arg(Dev, hipe_rtl:alu_dst(I), dst),
  io:format(Dev, " = ", []),
  case hipe_rtl:alu_op(I) of
    add -> io:format(Dev, "add ", []);
    sub -> io:format(Dev, "sub ", []);
    'or'-> io:format(Dev, "or ", []);
    'and' -> io:format(Dev, "and ", []);
    'xor' -> io:format(Dev, "xor ", []);
    'xornot' -> ok;
    andnot -> ok;
    sll -> io:format(Dev, "shl ", []);
    sllx -> ok;
    srl -> io:format(Dev, "lshr ", []);
    srlx -> ok;
    sra -> io:format(Dev, "ashr ", []);
    srax -> ok;
    Other -> exit({?MODULE, trans_alu,{"unknown ALU op", Other}})
  end,
  trans_arg(Dev, hipe_rtl:alu_src1(I)),
  io:format(Dev,", ",[]),
  trans_arg(Dev, hipe_rtl:alu_src2(I), dst),
  io:format(Dev,"~n",[]).

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
  io:format(Dev,"  ", []),
  io:format(Dev, "%res = ", []),
  io:format(Dev, "call {i32, i1} @llvm.sadd.with.overflow.i32(", []),
  trans_arg(Dev, hipe_rtl:alub_src1(I)),
  io:format(Dev,", ", []),
  trans_arg(Dev, hipe_rtl:alub_src2(I)),
  io:format(Dev,")~n", []),
  io:format(Dev,"  ", []),
  trans_arg(Dev, hipe_rtl:alub_dst(I), dst),
  io:format(Dev, " = ", []),
  io:format(Dev, "extractvalue {i32, i1} %res, 0~n", []),
  io:format(Dev,"  ", []),
  io:format(Dev, "%obit = extractvalue {i32, i1} %res, 1~n", []),
  io:format(Dev,"  ", []),
  io:format(Dev, "br i1 %obit, label %L~w, label %L~w~n",
    [hipe_rtl:alub_true_label(I), hipe_rtl:alub_false_label(I)]).

trans_alub_no_overflow(Dev, I) ->
  io:format(Dev,"  ", []),
  trans_arg(Dev, hipe_rtl:alub_dst(I), dst),
  io:format(Dev, " = ", []),
  case hipe_rtl:alub_op(I) of
    'or'-> io:format(Dev, "or ", []);
    'and' -> io:format(Dev, "and ", []);
    'xor' -> io:format(Dev, "xor ", []);
    'xornot' -> ok;
    andnot -> ok;
    sll -> io:format(Dev, "shl ", []);
    sllx -> ok;
    srl -> io:format(Dev, "lshr ", []);
    srlx -> ok;
    sra -> io:format(Dev, "ashr ", []);
    srax -> ok;
    Other -> exit({?MODULE, trans_alu,{"unknown ALU op", Other}})
  end,
  trans_arg(Dev, hipe_rtl:alub_src1(I)),
  io:format(Dev,", ",[]),
  trans_arg(Dev, hipe_rtl:alub_src2(I), dst),
  io:format(Dev,"~n",[]),
  %icmp 
  io:format(Dev, "  ", []),
  io:format(Dev, "%cond = ", []), %%TODO
  io:format(Dev, " icmp ~w ", [hipe_rtl:alub_cond(I)]),
  trans_arg(Dev, hipe_rtl:alub_src1(I)),
  io:format(Dev, ", ", []),
  trans_arg(Dev, hipe_rtl:alub_src2(I), dst),
  io:format(Dev, "~n", []),
  %br
  io:format(Dev, "  ", []),
  io:format(Dev, "br i1 %cond, ", []),
  io:format(Dev, "label %L~w, label %L~w~n", [hipe_rtl:alub_true_label(I),
      hipe_rtl:alub_false_label(I)]).

%%
%% branch
%%
trans_branch(Dev, I) ->
  %icmp 
  io:format(Dev, "  ", []),
  io:format(Dev, "%cond = ", []), %%TODO
  io:format(Dev, " icmp ~w ", [hipe_rtl:branch_cond(I)]),
  trans_arg(Dev, hipe_rtl:branch_src1(I)),
  io:format(Dev, ", ", []),
  trans_arg(Dev, hipe_rtl:branch_src2(I), dst),
  io:format(Dev, "~n", []),
  %br
  io:format(Dev, "  ", []),
  io:format(Dev, "br i1 %cond, ", []),
  io:format(Dev, "label %L~w, label %L~w~n", [hipe_rtl:branch_true_label(I),
      hipe_rtl:branch_false_label(I)]).

%%
%% call
%%
trans_call(Dev, I) ->
  io:format(Dev, "  ", []),
  trans_args(Dev, hipe_rtl:call_dstlist(I), dst),
  io:format(Dev, " = ", []),
  case hipe_rtl:call_fun(I) of
    '+' -> io:format(Dev, "add ", []);
    '-' -> io:format(Dev, "sub ", []);
    '*' -> io:format(Dev, "mul ", []);
    'div' -> io:format(Dev, "sdiv ", []);
    'rem' -> io:format(Dev, "srem ", []);
    Other -> exit({?MODULE, trans_call, {"unknown call", Other}})
  end,
  [H|T] =  hipe_rtl:call_arglist(I),
  trans_arg(Dev, H),
  io:format(Dev,", ",[]),
  trans_args(Dev, T, dst),
  io:format(Dev, "~n", []),
  case hipe_rtl:call_continuation(I) of
    [] -> true;
    CC -> trans_goto(Dev, hipe_rtl:mk_goto(CC))
  end.

%%
%% trans_comment
%%
trans_comment(Dev, I) ->
  io:format(Dev,"  ;;~p~n", [hipe_rtl:comment_text(I)]).

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
  io:format(Dev,"  ; gtest(",[]),
  trans_arg(Dev, hipe_rtl:gctest_words(I), dst),
  io:format(Dev,")~n",[]).

%%
%% goto
%%
trans_goto(Dev, I) ->
  io:format(Dev, "  ", []),
  io:format(Dev, "br label %L~w~n", [hipe_rtl:goto_label(I)]).

%%
%% label
%%
trans_label(Dev, I) ->
  io:format(Dev, "~nL~w:~n", [hipe_rtl:label_name(I)]).

%%
%% move
%%
trans_move(Dev, I) ->
  Dst = hipe_rtl:move_dst(I),
  Src = hipe_rtl:move_src(I),
  Src_type = arg_type(Src),
  %% %src_addr = alloca i32
  io:format(Dev, "  ", []),
  trans_arg(Dev, Src, dst),
  io:format(Dev, "_addr ", []),
  io:format(Dev, " = ", []),
  io:format(Dev, "alloca ~w~n", [Src_type]),
  %% store i32 src, i32* src_addr
  io:format(Dev, "  ", []),
  io:format(Dev, "store ", []),
  trans_arg(Dev, Src),
  io:format(Dev, ", ~w* ", [Src_type]),
  trans_arg(Dev, Src, dst),
  io:format(Dev, "_addr ~n", []),
  %% dst = load i32* src_addr
  io:format(Dev, "  ", []),
  trans_arg(Dev, Dst, dst),
  io:format(Dev, " = ", []),
  io:format(Dev, "load ~w* ", [Src_type]),
  trans_arg(Dev, Src, dst),
  io:format(Dev, "_addr~n", []).


%% 
%% phi
%%
trans_phi(Dev, I) ->
  io:format(Dev, "  ", []),
  trans_arg(Dev, hipe_rtl:phi_dst(I), dst),
  io:format(Dev, " = ", []),
  io:format(Dev, "phi ~w ", [arg_type(hipe_rtl:phi_dst(I))]),
  trans_phi_args(Dev, hipe_rtl:phi_arglist(I)),
  io:format(Dev, "~n", []).

%%
%% return 
%%
trans_return(Dev, I) ->
  io:format(Dev, "  ",  []),
  io:format(Dev, "ret ", []),
  trans_args(Dev, hipe_rtl:return_varlist(I)),
  io:format(Dev, "~n", []).


%%-----------------------------------------------------------------------------

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
    src -> io:format(Dev, "~w ", [arg_type(A)]);
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

trans_phi_args(_Dev, []) -> ok;
trans_phi_args(Dev, [{Pred, A}]) ->
  io:format(Dev, "[ ", []),
  trans_arg(Dev, A, dst),
  io:format(Dev, ", %L~w ]", [Pred]);
trans_phi_args(Dev, [{Pred, A} | Args]) ->
  io:format(Dev, "[ ", []),
  trans_arg(Dev, A, dst),
  io:format(Dev, ", %L~w ] , ", [Pred]),
  trans_phi_args(Dev, Args).


%% Return the type of arg A (only integers of 32 bits supported).
arg_type(A) ->
  case hipe_rtl:is_var(A) of
    true -> i32;
    false ->
      case hipe_rtl:is_reg(A) of
        true -> i32;
        false -> i32
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
  io:format(Dev, "%result = call i32 @~w(", [N]),
  init_params(Dev, erlang:length(Params)),
  io:format(Dev, ")~n", []),

  io:format(Dev, "%0 = tail call i32 (i8*, ...)* @printf(i8* noalias " ++ 
    "getelementptr inbounds ([3 x i8]* @.str, i64 0, i64 0)," ++ 
    " i32 %result) nounwind~n", []),
  io:format(Dev, "ret i32 %result~n}~n",[]),
  io:format(Dev, "declare i32 @printf(i8* noalias, ...) nounwind~n",[]),
  io:format(Dev, "declare {i32, i1} @llvm.sadd.with.overflow.i32(i32 %a, "++
    "i32%b)~n", []).

%% Print random parameters in main function
init_params(Dev, 1) -> 
  io:format(Dev,"i32 ~w",[random:uniform(10)]);
init_params(Dev, N) -> 
  io:format(Dev,"i32 ~w,",[random:uniform(10)]),
  init_params(Dev, N-1).
