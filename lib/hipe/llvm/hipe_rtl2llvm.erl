%% -*- erlang-indent-level: 2 -*-

-module(hipe_rtl2llvm).
-author("Chris Stavrakakis, Yiannis Tsiouris").
-include("../rtl/hipe_rtl.hrl").

-export([translate/1]).

translate(RTL) ->
    io:format("Geia sou llvm!~n"),
    {ok, File_rtl} = file:open("out.rtl", [append]),
    hipe_rtl:pp(File_rtl, RTL),
    file:close(File_rtl),

    {ok, File_llvm} = file:open("out.ll", [append]),
    Data = hipe_rtl:rtl_data(RTL),
    Code = hipe_rtl:rtl_code(RTL),
    translate_instrs(File_llvm, Code),
    file:close(File_llvm).

%%-----------------------------------------------------------------------------

translate_instrs(Dev, []) -> 
    ok;
translate_instrs(Dev, [I|Is]) ->
    translate_instr(Dev, I),
    translate_instrs(Dev, Is).


translate_instr(Dev, I) ->
  case I of
    #call{} -> trans_call(Dev, I);
    #return{} -> trans_return(Dev, I);
    #move{} -> trans_move(Dev, I);
    #label{} -> trans_label(Dev, I);
    #goto{} -> trans_goto(Dev, I);
    _ -> ok
  end.

%%-----------------------------------------------------------------------------

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
    _ -> ok
  end,
  trans_args(Dev, hipe_rtl:call_arglist(I)),
  io:format(Dev, "~n", []).      

%%
%% return 
%%
trans_return(Dev, I) ->
  io:format(Dev, "  ",  []),
  io:format(Dev, "ret ", []),
  trans_args(Dev, hipe_rtl:return_varlist(I)),
  io:format(Dev, "~n", []).

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
%% label
%%
trans_label(Dev, I) ->
  io:format(Dev, "L~w:~n", [hipe_rtl:label_name(I)]).

%%
%% goto
%%
trans_goto(Dev, I) ->
  io:format(Dev, "  ", []),
  io:format(Dev, "br label L~w~n", [hipe_rtl:goto_label(I)]).

%%-----------------------------------------------------------------------------

%% 
%% Prety print arg(s).
%%
trans_args(Dev, A) ->
  trans_args(Dev, A, src).
%%
trans_args(Dev, [], Type) ->
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
    dst -> ok;
    _ ->   ok %% fail (not so ok!)
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
	      Val = hipe_tagscheme:fixnum_val(hipe_rtl:imm_value(A)),
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
