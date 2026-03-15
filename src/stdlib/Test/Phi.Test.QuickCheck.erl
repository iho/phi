%%---------------------------------------------------------------------------
%% |
%% Module      :  QuickCheck
%% Copyright   :  (c) 2020-2021 EMQ Technologies Co., Ltd.
%% License     :  BSD-style (see the LICENSE file)
%%
%% Maintainer  :  Feng Lee, feng@emqx.io
%%                Yang M, yangm@emqx.io
%% Stability   :  experimental
%% Portability :  portable
%%
%% The QuickCheck FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.Test.QuickCheck').

-export([ seed/1
        , mkRand/1
        , seed/3
        , split/1
        , next/1
        , uniform/1
        , randomRFloat/2
        , uniform_s/1
        , randomRInt/2
        , randomRChar/2
        , genPure/1
        , genBind/2
        , randomRIO/2
        , isIO/1
        , pureIO/1
        , mapListImpl/2
        , indexImpl/2
        ]).

%% Gen monad pure: wrap value in a Gen that always returns it.
genPure(V) -> {'Gen', fun(_, _) -> V end}.

%% Gen monad bind: run Gen M, pass result to F, run the resulting Gen.
genBind({'Gen', M}, F) ->
    {'Gen', fun(I, R) ->
        A = M(I, R),
        try case F(A) of
            {'Gen', G} -> G(I, R);
            IOFun when is_function(IOFun, 0) -> IOFun()
        end
        catch E:Err ->
            Msg = iolist_to_binary(io_lib:format("~p:~p", [E, Err])),
            {'Result', #{ok => 'Nothing', stamp => [], arguments => [Msg]}}
        end
    end};
genBind(_, _) ->
    %% Non-Gen first argument (e.g. IO action from broken dispatch): return crash Gen.
    {'Gen', fun(_, _) -> {'Result', #{ok => 'Nothing', stamp => [], arguments => [<<"gen_type_error">>]}} end}.

%% isIO(V): true if V is a 0-arity fun (an IO action), false otherwise.
isIO(V) -> is_function(V, 0).

%% pureIO(V): wrap V in an IO thunk (0-arity fun returning V).
pureIO(V) -> fun() -> V end.

%% mapListImpl(F, Xs): map F over a list using lists:map.
mapListImpl(F, Xs) -> lists:map(F, Xs).

%% indexImpl(I, Xs): 0-indexed list access using lists:nth.
indexImpl(I, Xs) -> lists:nth(I + 1, Xs).

%% randomRIO(Lo, Hi) -> IO Integer: returns an IO action that picks a random integer in [Lo, Hi].
randomRIO(Lo, Hi) ->
    fun() ->
        Range = Hi - Lo + 1,
        Lo + (rand:uniform(Range) - 1)
    end.

-define(PRIME1, 30269).
-define(PRIME2, 30307).
-define(PRIME3, 30323).

%%-----------------------------------------------------------------------
%% The type of the state

%% -type seed() :: {integer(), integer(), integer()}.

%%-----------------------------------------------------------------------

mkRand(V) -> seed(V).

seed(Int) when is_integer(Int) ->
  A1 = (Int bsr 16) band 16#fffffff,
  A2 = Int band 16#ffffff,
  A3 = (Int bsr 36) bor (A2 bsr 16),
  seed(A1, A2, A3);
seed({A1, A2, A3}) -> seed(A1, A2, A3).

seed(A1, A2, A3) ->
  ({(abs(A1) rem (?PRIME1-1)) + 1,   % Avoid seed numbers that are
    (abs(A2) rem (?PRIME2-1)) + 1,   % even divisors of the
    (abs(A3) rem (?PRIME3-1)) + 1}). % corresponding primes.

split({A1, A2, A3}) ->
  B1 = (A1*171) rem ?PRIME1,
  B2 = (A2*172) rem ?PRIME2,
  B3 = (A3*170) rem ?PRIME3,
  V1 = seed(B1*B2+B1+B2+1332292274972041455),
  V2 = seed(B2*B3+B2+B3+7304856964418773083),
  {V1, V2}.

next({A1, A2, A3}) ->
  B1 = (A1*171) rem ?PRIME1,
  B2 = (A2*172) rem ?PRIME2,
  B3 = (A3*170) rem ?PRIME3,
  {B1, B2, B3}.

uniform({A1, A2, A3}) ->
  B1 = (A1*171) rem ?PRIME1,
  B2 = (A2*172) rem ?PRIME2,
  B3 = (A3*170) rem ?PRIME3,
  R = B1/?PRIME1 + B2/?PRIME2 + B3/?PRIME3,
  R - trunc(R).

randomRInt({A,B}, Seed) ->
  T = B-A+1,
  V = uniform(T, Seed),
  A+V-1.

randomRChar({A,B}, Seed) ->
  T = B-A+1,
  V = uniform(T, Seed),
  A+V-1.

randomRFloat({A,B}, Seed) ->
  T = B-A,
  V = uniform_s(Seed)*T+A,
  V.

uniform(N, Seed) when is_integer(N), N >= 1 ->
  trunc(uniform(Seed) * N) + 1.

uniform_s({A1, A2, A3}) ->
  R = A1/?PRIME1 + A2/?PRIME2 + A3/?PRIME3,
  R - trunc(R).
