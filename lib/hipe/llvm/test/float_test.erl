-module(float_test).
-compile(export_all).

afloat() -> 1.0.
afloat(X) -> X+2.0.
afloat(X,Y) -> X+Y.
afloat(X,Y,Z) when is_float(X) -> X+Y+Z.
afloat(X,Y,Z,W) -> X/Y+Z/W.
