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
        #alu{} -> io:fwrite(Dev, "~s~n", ["Found an alu"]);
        _ -> ok
    end.


