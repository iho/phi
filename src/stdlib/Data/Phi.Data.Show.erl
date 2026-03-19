%%---------------------------------------------------------------------------
%% |
%% Module      :  Show
%% Copyright   :  (c) 2020-2021 EMQ Technologies Co., Ltd.
%% License     :  BSD-style (see the LICENSE file)
%%
%% Maintainer  :  Feng Lee, feng@emqx.io
%%                Yang M, yangm@emqx.io
%% Stability   :  experimental
%% Portability :  portable
%%
%% The Show FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.Data.Show').

-export([ showAtomImpl/1
        , showIntImpl/1
        , showFloatImpl/1
        , showNumImpl/1
        , showCharImpl/1
        , showAny/1
        , isFloatVal/1
        , isIntegerVal/1
        , isListVal/1
        , isBinaryVal/1
        , isAtomVal/1
        ]).

%% Atom -> String
-spec(showAtomImpl(any()) -> binary()).
showAtomImpl(A) when is_atom(A) -> atom_to_binary(A, utf8);
showAtomImpl(A) -> list_to_binary(lists:flatten(io_lib:format("~p", [A]))).

%% Integer -> String
-spec(showIntImpl(integer()) -> binary()).
showIntImpl(I) -> integer_to_binary(I).

%% Float -> String
-spec(showFloatImpl(float()) -> binary()).
showFloatImpl(F) ->
  list_to_binary(erlang:float_to_list(F, [{decimals,precision(abs(F), 0)}])).

%% Float -> String
-spec(showNumImpl(number()) -> binary()).
showNumImpl(N) when is_integer(N) ->
  showIntImpl(N);
showNumImpl(N) when is_float(N) ->
  showFloatImpl(N).

%% showChar :: Char -> String
-spec(showCharImpl(char()) -> binary()).
showCharImpl(C) -> list_to_binary([$', C, $']).

precision(A, P) ->
  case A == trunc(A) of
    true  -> P;
    false -> precision(A*10.0, P+1)
  end.

-spec(showAny(any()) -> binary()).
showAny(A) -> list_to_binary(lists:flatten(io_lib:format("~p", [A]))).

isFloatVal(X) -> is_float(X).
isIntegerVal(X) -> is_integer(X).
isListVal(X) -> is_list(X).
isBinaryVal(X) -> is_binary(X).
isAtomVal(X) -> is_atom(X).
