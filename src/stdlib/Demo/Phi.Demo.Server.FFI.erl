-module('Phi.Demo.Server.FFI').

-behaviour(gen_server).

-include("../Phi.Foreign.hrl").

-export([startServer/0]).
-export([init/1, handle_call/3, handle_cast/2, handle_info/2, terminate/2, code_change/3]).

startServer() ->
    ?IO(begin
        {ok, Pid} = gen_server:start_link({local, server}, ?MODULE, [], []),
        Pid
    end).

init([]) ->
    {ok, 20}.

handle_call('Query', _From, State) ->
    io:format("Call: Query~n"),
    {reply, {'QueryResult', State}, State};
handle_call(_Req, _From, State) ->
    {stop, badRequest, State}.

handle_cast('Inc', State) ->
    {noreply, State + 1};
handle_cast('Dec', State) ->
    {noreply, State - 1};
handle_cast(_Msg, State) ->
    {noreply, State}.

handle_info(_Info, State) ->
    {noreply, State}.

terminate(_Reason, _State) ->
    ok.

code_change(_OldVsn, State, _Extra) ->
    {ok, State}.
