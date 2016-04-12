%% @author Me
%% @doc @todo Add description to main.


-module(main).

%% ====================================================================
%% API functions
%% ====================================================================
-export([run1/1,run2/1,run3/1,run4/1,run5/1,run6/1,run7/1,run8/1,run9/1,proof_by_resolution/0]).

%"(A => B) and (B => C) |- (A => C)"
%"(A => (A => B)) and ((A => B) => not B) |- (A => not B)"
%% ====================================================================
%% Internal functions
%% ====================================================================

%% ====================================================================
%% ====================================================================
%% =======================FULL IMPLEMENTATION==========================
%% ====================================================================
%% ====================================================================
proof_by_resolution()
  ->String = "((A or B) and (A => C) and (B => C)) |- C",
	[H|T]  = string:tokens(String, "|-"),
	S = lists:flatten(lists:concat([["not "], T])),
	Resolution_clause = main:run9(S),
	Clausal_list = main:run9(H),	
	Final_list = lists:append(Clausal_list, Resolution_clause),
	io:format("Clauses in CNF:~n~p~n~n",[Final_list]),
	theoremprover:prover(Final_list, [],[]).
%% ====================================================================
%% ====================================================================
%% ====================================================================
%% ====================================================================

run1(String)
  ->theoremprover:tokenize(String).
	
run2(String)
  ->theoremprover:parseExpr(run1(String),[]).

run3(String)
  ->theoremprover:ie(run2(String)).

run4(String)
  ->theoremprover:dm(run3(String)).

run5(String)
  ->theoremprover:dne(run4(String)).

run6(String)
  ->theoremprover:ald(run5(String)).

run7(String)
  ->theoremprover:re(run6(String)).

run8(String)
  ->theoremprover:rc(run7(String)).

run9(String)
  ->theoremprover:gcl(run8(String),[]).


