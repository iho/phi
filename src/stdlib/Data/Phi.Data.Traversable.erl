%%---------------------------------------------------------------------------
%% |
%% Module      :  Traversable
%% License     :  BSD-style (see the LICENSE file)
%%
%% The Traversable FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.Data.Traversable').

-export([mapMImpl/2]).

%% mapMImpl f l = seqio (map f l)
%% Applies f to each element of the list (using lists:map for correct list
%% functor semantics), then sequences the resulting IO actions.
mapMImpl(F, L) ->
    'Phi.Control.Monad.FFI':seqio(lists:map(F, L)).
