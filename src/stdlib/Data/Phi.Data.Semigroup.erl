%%---------------------------------------------------------------------------
%% |
%% Module      :  Semigroup
%% Copyright   :  (c) 2020-2021 EMQ Technologies Co., Ltd.
%% License     :  BSD-style (see the LICENSE file)
%%
%% Maintainer  :  Feng Lee, feng@emqx.io
%%                Yang M, yangm@emqx.io
%% Stability   :  experimental
%% Portability :  portable
%%
%% The Semigroup FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.Data.Semigroup').

-export([ stringAppend/2
        , listAppend/2
        , semiAppend/2
        ]).

%% stringAppend :: String -> String -> String
-spec(stringAppend(string(), string()) -> string()).
stringAppend(S1, S2) -> string:concat(S1, S2).

%% listAppend :: forall a. List a -> List a -> List a
-spec(listAppend(list(), list()) -> list()).
listAppend(L1, L2) -> lists:append(L1, L2).

%% semiAppend/2: runtime-dispatched Semigroup append for all built-in instances.
%% This is used by the <> operator when static type information is unavailable.
semiAppend({ok}, _) -> {ok};                                   %% Unit
semiAppend(A, B) when is_binary(A) ->
    iolist_to_binary([A, B]);                                  %% String / Binary
semiAppend(A, B) when is_list(A) ->
    A ++ B;                                                    %% List
semiAppend({A1, B1}, {A2, B2}) ->
    {semiAppend(A1, A2), semiAppend(B1, B2)};                  %% 2-Tuple
semiAppend(A, B) when is_map(A) ->
    maps:merge(A, B);                                          %% Map / OrdDict fallback
semiAppend(_, _) -> {ok}.                                      %% fallback Unit
