%%---------------------------------------------------------------------------
%% |
%% Module      :  Dict
%% Copyright   :  (c) 2020-2021 EMQ Technologies Co., Ltd.
%% License     :  BSD-style (see the LICENSE file)
%%
%% Maintainer  :  Feng Lee, feng@emqx.io
%%                Yang M, yangm@emqx.io
%% Stability   :  experimental
%% Portability :  portable
%%
%% The Dict FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.Control.Process.Dict').

-include("../../Phi.Foreign.hrl").

-compile(no_auto_import).

-export([ erase/1
        , eraseAll/0
        , get/1
        , put/2
        ]).


erase(Key) ->
  ?IO('Maybe':'maybe'(erlang:erase(Key))).

eraseAll() ->
  ?IO(begin erlang:erase(), ok end).

get(Key) ->
  ?IO('Maybe':'maybe'(erlang:get(Key))).

put(Key, Val) ->
  ?IO('Maybe':'maybe'(erlang:put(Key, Val))).
