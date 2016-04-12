%% @author Me
%% @doc @todo Add description to 'Parser'.


-module('theoremprover').

%% ====================================================================
%% API functions
%% ====================================================================
-export([tokenize/1, parseExpr/2,ie/1,dm/1,dne/1,ald/1,re/1,rc/1,gcl/2,unify/5,negate/1,get_resolvents/4,prover/3]).


%% ====================================================================
%% Internal functions
%% ====================================================================


%% ====================================================================
%% 								PART ONE
%% ====================================================================

tokenize([])
  -> [];
tokenize([$(|T]) 
  -> [{bracket,openbracket} | tokenize(T)];
tokenize([$)|T]) 
  -> [{bracket, closebracket } | tokenize(T)];
tokenize([H|T]) when (H>=$A) andalso (H=<$Z)
  -> [{proposition,[H]} | tokenize(T)];
tokenize("=>"++ T) 
  -> [{connective,implication} | tokenize(T)];
tokenize("<=>"++ T) 
  -> [{connective,equivalence} | tokenize(T)];
tokenize("and" ++ T) 
  -> [{connective,conjunction} | tokenize(T)];
tokenize("or" ++ T) 
  -> [{connective,disjunction} | tokenize(T)];
tokenize("not" ++ T) 
  -> [{connective,negation} | tokenize(T)];
tokenize("|-"++T)
  ->[{connective,finalImplication} | tokenize(T)];
tokenize([_|T]) 
  -> tokenize(T).

%%_________________________________________________________________________________
%%               PARSER
%%_________________________________________________________________________________

parseExpr([],[H|[]])
  ->H;

parseExpr([],[H|T])
  ->{H,parseExpr([],T)};

parseExpr([{bracket,openbracket},{proposition,P},{bracket,closebracket}|Tail],Stack)
  -> parseExpr([P|Tail],Stack);

parseExpr([{proposition,P}|Tail],Stack)
  -> parseExpr(Tail, [{pos,P}|Stack]);

parseExpr([{connective,C}|Tail],[One,Two|Rest]) when One =:= negation 
  -> [C, {negation,Two}, parseExpr(Tail, Rest)];

parseExpr([{connective,C}|Tail],[Top|Rest]) 
  -> [C, Top, parseExpr(Tail, Rest)];

parseExpr([{connective,negation},{proposition,P}|Tail],Stack) 
  -> First   = [P|Stack], 
	 Second  = [negation|First], 
	 parseExpr(Tail, Second);

parseExpr([{connective,negation},{bracket,openbracket}|Tail],Stack) 
  -> [negation,parseExpr([{bracket,openbracket}|Tail], Stack)];

parseExpr([{connective,C}|Tail],[]) 
  -> [C, parseExpr(Tail, [])];

parseExpr([{bracket,openbracket}|Tail],Stack) 
  -> First  = findNextBracket(Tail,[]), 
	 Second = findTail(Tail), 
	 parseExpr(Second, [parseExpr(First,[])|Stack]);

parseExpr([{bracket,closebracket}|Tail],Stack) 
  -> parseExpr(Tail,Stack).



findTail([])
  ->[];
findTail([{bracket,closebracket}|Tail])
  ->Tail;
findTail([_|T])
  ->findTail(T).

findNextBracket([{bracket,closebracket}|_],List)
  ->List;
findNextBracket([],List)
  -> List;
findNextBracket([H|T] , List)
  ->NewL = List ++ [H],
	findNextBracket(T ,NewL).

%% =============================================================
%% 							PART TWO
%% =============================================================
%%______________________________________________________________
%%               				CNF
%%______________________________________________________________
%%--------------------------------------------------------------
%% Step 1: Eliminate Implications  													
%%--------------------------------------------------------------
%%	Transform any proposition of the form 
%%	A => B to not A or B			       
%%	and any proposition of the form 
%%	A <=> B to (not A or B) and (not B or A)	
%%--------------------------------------------------------------  

ie([conjunction, A, B])
  ->[conjunction, ie(A), ie(B)];

ie([disjunction, A, B])
  ->[disjunction, ie(A), ie(B)];

ie([implication, A, B])
  ->[disjunction, [negation, ie(A)], ie(B)];

ie([equivalence, A, B])
  ->[conjunction, ie([implication,A,B]), ie([implication,B,A])];

ie([negation, A])
  ->[negation, ie(A)];

ie([A])
  ->A;

ie(A)
  ->A.

%%--------------------------------------------------------------
%% Step 2: DeMorgan Laws 													
%%--------------------------------------------------------------
%%	Push negations of parenthesised expressions inwards by 
%%	transforming any proposition of the form 
%%	not(A or B) to not A and not B 
%%	and any proposition of 
%%	the form not(A and B) to not A or not B		       	
%%--------------------------------------------------------------  
dm([conjunction,A,B])
  ->[conjunction,dm(A),dm(B)];

dm([disjunction,A,B])
  ->[disjunction,dm(A),dm(B)];

dm([negation,[conjunction,B,C]])
  ->[disjunction,dm([negation,B]),dm([negation,C])];

dm([negation,[disjunction,D,E]])
  ->[conjunction,dm([negation,D]),dm([negation,E])];

dm([negation,{pos,P}])
  ->{negation,P};

dm([negation,[{pos,P}]])
  ->{negation,P};

dm([A])
  ->A;

dm(A)
  ->A.

%%--------------------------------------------------------------
%% Step 3: Double negation elimination 													
%%--------------------------------------------------------------
%%	Transform any proposition of the form not not A to A			       	
%%--------------------------------------------------------------  
dne([conjunction,A,B])
  ->[conjunction,dne(A),dne(B)];

dne([disjunction,A,B])
  ->[disjunction,dne(A),dne(B)];

dne([negation,[negation,A]])
  ->dne(A);

dne([negation,{negation,A}])
  ->{pos,A};

dne([negation,[{negation,A}]])
  ->{pos,A};

dne(A)
  ->A.

%%--------------------------------------------------------------
%% Step 4: Algebraic Distribution													
%%--------------------------------------------------------------
%%	Distribute conjunctions over disjunctions by transforming
%%	any proposition of the form 
%%	A or (B and C) to (A or B) and (A or C) 
%%	and any propositionof the form 
%%	(A and B) or C to (A or C) and (B or C).	       	
%%--------------------------------------------------------------  

ald([conjunction,A,B])
  ->[conjunction,ald(A),ald(B)];

ald([disjunction,[conjunction,C,D],B]) 
  ->[conjunction,ald([disjunction,ald(C),ald(B)]),ald([disjunction,ald(D),ald(B)])];

ald([disjunction,A,[conjunction,C,D]])
  ->[conjunction,ald([disjunction,ald(A),ald(C)]),ald([disjunction,ald(A),ald(D)])];

ald(A)
  ->A.

%%--------------------------------------------------------------
%% Step 5: Repetition elimination 													
%%--------------------------------------------------------------
%%	Transform any proposition of the form (A or A) to A			       	
%%--------------------------------------------------------------  

re([conjunction,A,A])
  ->[conjunction,re(A)];

re([conjunction,A,B])
  ->[conjunction,re(A),re(B)];

re([disjunction,A,B])
  ->lists:flatten( [rd(lists:flatten([disjunction,A,B]))]);

re(A)
  ->A.

%%Remove duplicates method from StackExchange

rd([])    
  -> [];
rd([H|T]) 
  -> [H | [X || X <- rd(T), X /= H]].

%%--------------------------------------------------------------
%% Step 6: Remove connectives												
%%--------------------------------------------------------------

rc([conjunction,A])
  ->[rc(A)];

rc([conjunction,A,B])
  ->[[rc(A)],[rc(B)]];

rc([disjunction|T])
  ->T;

rc(A)
  ->[A].

%%--------------------------------------------------------------
%% Step 7: Get clause list												
%%--------------------------------------------------------------
gcl([],L)
  ->L;
 
gcl([[[H|T]|T2]|T3] ,FinalList) 
  ->case listFind([[H|T]|T2]) of
    true 
	  ->if
			is_list([H|T]) 
			  ->L1 =gcl([H|T],FinalList),
				gcl([T2|T3],L1);
			true 
			  ->Fl = lists:append(FinalList,[[H|T]]),
				gcl([T2|T3],Fl) 
		end;
    false 
	  ->Fl2 =  lists:append(FinalList,[[[H|T]|T2]]),
		gcl(T3,Fl2)
	end;

gcl([[H|T]|T2] ,FinalList) 
  ->case listFind([H|T]) of
    true 
	  ->if
			is_list(H) 
			  ->L1 = gcl(H,FinalList),
				gcl([[T|T2]],L1);
			true 
			  -> Fl = lists:append(FinalList,[[H]]),
				 gcl([T|T2],Fl)
		end;
    false 
	  ->Fl2 =  lists:append(FinalList,[[H|T]]),
		gcl(T2,Fl2)
	end;

gcl([H|T] ,FinalList) 
  ->case listFind([H|T]) of
		true 
		  ->if
				is_list(H) 
				  ->L1 = gcl(H,FinalList),
					gcl(T,L1);
				true 
				  ->Fl = lists:append(FinalList,[[H]]),
					gcl(T,Fl)
			end;
		false 
		  ->Fl2 =  lists:append(FinalList,[[H|T]]),
			Fl2
	end.
 
listFind ([]) 
  ->false;
 
listFind([Item|ListTail]) 
  ->case ( is_list(Item) ) of
		true    
		  ->true;
		false   
		  ->listFind(ListTail)
	end.

%% =====================================================================
%% 								PART THREE
%% =====================================================================
%%_______________________________________________________________________
%%                  		 	RESOLUTION
%%_______________________________________________________________________
%%	Take two clauses and apply the resolution rule, output is the 
%%	resulting clause if resolution is possible. If [] is a member
%%	of the final output, then we have proof.
%%_______________________________________________________________________

unify ( First_clause, Second_clause , [] , [], [] )
   ->NegatedClause = negate ( First_clause ),
	 unify ( NegatedClause, Second_clause, [], [First_clause, Second_clause], Second_clause);

unify ([A|[]], [A|[]], Output, _, _)
  ->Output;

unify(_, _, Output, _, [])
  ->case len(Output) /= 0 of
		true
		  ->Output;
		false
		  ->ok
	end;


unify ([A|First_clause_T], [A|Second_clause_T] , Output , Initial, Not_considered )
  ->New_notconsidered = Not_considered -- [A],
 	New_output = lists:append( Output, [ lists:flatten( [ negate(First_clause_T) | Second_clause_T])]),
 	unify( First_clause_T ++ [A], Second_clause_T ++ [A], New_output, Initial, New_notconsidered);
 
unify ([A|First_clause_T], [B|Second_clause_T] , Output , Initial, Not_considered )
  ->New_notconsidered = Not_considered -- [B],
 	unify( [A|First_clause_T], Second_clause_T ++ [B], Output, Initial, New_notconsidered).

len([]) 
  -> 0;
len([_|T]) 
  -> 1 + len(T).

negate([])
  ->[];

negate([H|T])
  ->case H of 
		{negation,Prop}
		  ->[{pos,Prop}|negate(T)];
		{pos,Prop}
		  ->[{negation, Prop}|negate(T)]
	end.
 
%% =====================================================================
%% 								PART FOUR
%% =====================================================================
%%_______________________________________________________________________
%%                   			  Prover
%%_______________________________________________________________________
%%	Takes expression, and apply the resolution rule, output is true if
%%	contradiction is found, exhaustion if not
%%_______________________________________________________________________


get_resolvents(_,[],_,Output)
  ->Output;
get_resolvents(Clause,[Clausal_list_H|Clausal_list_T],Not_considered,Output)
  ->L = unify(Clause,Clausal_list_H,[],[],[]),
	case L =:= ok of
		true
		  ->get_resolvents(Clause,Clausal_list_T,Not_considered -- [Clausal_list_H],Output);
		false
		  ->N=lists:flatten(L),
			get_resolvents(Clause,Clausal_list_T,Not_considered -- [Clausal_list_H],Output ++ [N])
	end.


  
prover([Clausal_list_H|Clausal_list_T], [], [])
  ->prover(Clausal_list_H,Clausal_list_H,Clausal_list_T);

prover(_, Considered_resolution_clauses, [Remainder_H|Remainder_T])
  ->New_Resolution_clause = Remainder_H,
	New_Considered_resolution_clauses = Considered_resolution_clauses ++ [New_Resolution_clause],
	Resolvents = get_resolvents(New_Resolution_clause,Remainder_T,[],[]),%filter resolvents to check if exist in remainder or in considered
	Remainder = Remainder_T ++ [Resolvents],
	case lists:member([], Remainder) of
		true
		  ->io:format("Contradiction found while searching~n~nResolvent clauses considered:~n~p~n",[Remainder]);
		false
		  ->prover(New_Resolution_clause, New_Considered_resolution_clauses, Remainder)
	end.
	


%% As a running example, we prove the tautology 
%% ((A or B) and (A => C) and (B => C)) |- C
%% by deriving a contradiction from the clausal list 
%% [[A, B], [not A, C], [not B, C], [not C]].
%% 
%% 1. The data types we keep track of:
%%
%% The clause currently being used to generate resolvents (the resolution clause) -
%% initialised to [] .
%%
%% A list of the resolution clauses which have already been considered - initialised
%% to [].
%%
%% The remainder of the clausal list - initialised to the full clausal list.
%%
%% 2. The first clause from the remainder is set as the resolution clause - in this case
%% [A, B]. We add the resolution clause to the list of already-considered clauses and
%% delete it from the remainder, leaving [[not A, C], [not B, C], [not C]]. Alternately, if the
%% remainder is the empty list before the resolution clause is set, the algorithm terminates
%% under the exhaustion condition.
%%
%% 3.Here, part three is used to get the resolvents, here the single resolvent [C, B].
%%
%% 4. The resolvents are filtered against the clauses in the remainder and those resolution
%% clauses already considered - if any of the resolvents are a permutation of any of
%% these clauses, they represent no new information and as such are excluded. Those
%% remaining resolvents (if any) are added to the remainder - [C, B] is not a permutation
%% of any of [not A, C], [not B, C], [not C] or [A, B] and so is added.
%%
%% 5. At this point, if [] was one of the resolvents added to the remainder, we have derived
%% our contradiction and the algorithm terminates under the contradiction condition. 
%% Otherwise, there are two scenarios:
%%
	%% A-New resolvents were inferred - the resolution constant is appended to the end of
	%% the resolution clause, here giving us [B, A], and the algorithm goes back to step
	%% 3. However, if all constants of the resolution clause have been considered, the
	%% algorithm moves to the scenario below.
%%
	%% B-No new resolvents were inferred - the algorithm goes back to step 2.
	%% Continuing this algorithm, the example given runs from start to finish as follows:

%% Proof: ((A or B) and (A => C) and (B => C)) |- C

%% Res.Constant 	Res.Clause 		Remainder 									Resolvents
%% A 				[A, B] 			[[not A, C], [not B, C], [not C]] 			[C, B]
%% B 				[B, A] 			[[not A, C], [not B, C], [not C], [C, B]] 	[C, A]
%% not A 			[not A, C] 		[[not B, C], [not C], [C, B], [C, A]] 		[C]
%% C 				[C, not A] 		[[not B, C], [not C], [C, B], [C, A], [C]] 	[not A]
%% not B 			[not B, C] 		[[not C], [C, B], [C, A], [C], [not A]]
%% not C 			[not C] 		[[C, B], [C, A], [C], [not A]] 				[B], [A], []
%% 

%% After inferring [], the algorithm terminates and the proof by contradiction is complete.

	
	
	

	
	
