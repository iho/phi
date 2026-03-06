%%---------------------------------------------------------------------------
%% |
%% Module      :  Runtime.Receive
%% Copyright   :  (c) 2020-2021 EMQ Technologies Co., Ltd.
%% License     :  BSD-style (see the LICENSE file)
%%
%% Maintainer  :  Feng Lee, feng@emqx.io
%%                Yang M, yangm@emqx.io
%% Stability   :  experimental
%% Portability :  portable
%%
%% The Receive FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.Runtime.Receive').

-include("../Phi.Foreign.hrl").

-export([receiveWith/3]).

receiveWith(MatcherFun, Timeout, AfterFun) ->
    ?IO(receive
        Msg -> (MatcherFun(Msg))()
    after Timeout ->
        (AfterFun())()
    end).
