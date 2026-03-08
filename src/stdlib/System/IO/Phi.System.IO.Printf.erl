%%---------------------------------------------------------------------------
%% |
%% Module      :  Printf
%% Copyright   :  (c) 2020-2021 EMQ Technologies Co., Ltd.
%% License     :  BSD-style (see the LICENSE file)
%%
%% Maintainer  :  Feng Lee, feng@emqx.io
%%                Yang M, yangm@emqx.io
%% Stability   :  experimental
%% Portability :  portable
%%
%% The Printf FFI module.
%%
%%---------------------------------------------------------------------------
-module('Phi.System.IO.Printf').

-include("../../Phi.Foreign.hrl").

-export([ print/1
        , println/1
        , println_/1
        ]).

print(S) -> ?IO(io:format(S)).

println(S) -> ?IO(io:format("~ts~n", [S])).

println_(S) -> ?IO(io:format("~ts~n",[S])).
