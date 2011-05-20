-module(atom_test).
-compile(export_all).

ret_atom() -> ok.

ret_string(X) -> X++atom_to_list(ok).

ret_tuple(X,_) -> {ok, {atom1, X}, foo_42}.

