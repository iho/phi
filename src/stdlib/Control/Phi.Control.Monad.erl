%%---------------------------------------------------------------------------
%% |
%% Module      :  Monad
%% Copyright   :  (c) 2020-2021 EMQ Technologies Co., Ltd.
%% License     :  BSD-style (see the LICENSE file)
%%
%% Maintainer  :  Feng Lee, feng@emqx.io
%%                Yang M, yangm@emqx.io
%% Stability   :  experimental
%% Portability :  portable
%%
%% The Monad FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.Control.Monad').

-export([ applyListImpl/2
        , listAppend/2
        , bindImpl/2
        , bindListImpl/2
        , fmapImpl/2
        , pureImpl/1
        , seqio/1
        , seqio_/1
        , unsafePerformIO/1
        , replApply/1
        ]).

-type(mapFun() :: fun((A :: any()) -> B :: any())).

-spec(applyListImpl(list(mapFun()), list(any())) -> list(any())).
applyListImpl(Funs, L) ->
  [F(X) || X <- L, F <- Funs].

-spec(listAppend(list(A :: any()), list(A :: any())) -> list(A :: any())).
listAppend(A, B) -> lists:append(A, B).

-spec(bindImpl(any(), fun((A :: term()) -> B :: term())) -> any()).
bindImpl({'Gen', M}, F) ->
    %% Gen monad bind: run generator M, pass value to F, run resulting generator.
    %% Gen inner functions are curried 1-arity: fun(I) -> fun(R) -> val end end.
    {'Gen', fun(I) -> fun(R) ->
        A = (M(I))(R),
        case F(A) of
            {'Gen', G} -> (G(I))(R);
            IOFun when is_function(IOFun, 0) -> IOFun()
        end
    end end};
bindImpl(X, F) ->
    %% IO monad bind: wrap in a 0-arity fun for lazy execution.
    fun() -> case F(X()) of
                 {'Gen', _} = Gen -> Gen;  % shouldn't happen but be safe
                 IOResult when is_function(IOResult, 0) -> IOResult();
                 V -> V
             end
    end.

-spec(fmapImpl(fun((A :: any()) -> B :: any()), any()) -> any()).
fmapImpl(F, Ma) -> fun() -> F(Ma()) end.

-spec(bindListImpl(list(term()), fun((term()) -> list(term()))) -> list(term())).
bindListImpl(L, F) -> lists:append(lists:map(F, L)).

-spec(pureImpl(any()) -> any()).
pureImpl(X) -> fun() -> X end.

seqio(L) when is_list(L) ->
  fun() -> [V() || V <- L] end.

seqio_(L) when is_list(L) ->
  fun() -> [V() || V <- L], ok end.

unsafePerformIO(L) -> L().

replApply(F) ->
  case is_function(F) andalso (arity(F) == 0) of
    true -> F();
    false -> F
  end.

arity(F) ->
  element(2, erlang:fun_info(F, arity)).
