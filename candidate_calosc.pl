known_fact(brat(andrzej, aneta)).
known_fact(brat(marian, aneta)).
known_fact(maz(mikolaj, aneta)).
known_fact(szwagier(mikolaj, andrzej)).

predicate(brat,2).
predicate(maz,2).

learn( Predicate, NegExamples)  :-
   gen_positive(PosExamples),
   get_negative(Predicate, PosExamples, NegExamples).
   %learn( Rule, PosExamples, NegExamples, Vars, Description),                                     
   %nl, write( Class), write('  <== '), nl,                                   
   %writelist( Description),
   %assert( Class  <==  Description).                                      

gen_positive(PosExamples):-
	findall(X, is_pos(X), PosExamples).
	
is_pos(X):-
	known_fact(X),
	functor(X, Functor, _),
	not(predicate(Functor,_)).

get_negative(Predicate, PosExamples, NegExamples):-
	setof(X, get_objects(X), Objects),
	findall(Y, get_neg(Predicate, Objects, PosExamples, Y), NegExamples).
	
	
get_objects(X) :-
	known_fact(Z),
	Z =.. [_|Args],
	get_name(Args, X).

get_name([X], X).
get_name([X|_], X).
get_name([_|RestArgs], X) :-
	get_name(RestArgs, X).
	
get_neg(Predicate, Objects, PosExamples, Neg):-
	member(M1, Objects),
	member(M2, Objects),
	M1 \= M2,
	Neg =.. [Predicate, M1, M2],
	not(member(Neg, PosExamples)).
   
learn(Rule, [], _, _, Rule).               

learn( Rule, PosExamples, NegExamples, Vars, [NewRule | NewRules])  :-
   learn_conj( Rule, PosExamples, NegExamples, Vars,NewRule, _),
   remove( PosExamples, NewRule, RestPosExamples),                       
   learn( Rule, RestPosExamples, NegExamples, Vars, NewRules).   

remove( [], _, []).

remove( [Example | Examples1], Rule, Examples1)  :-
   covers(Rule, Example), !,                                        
   remove( Example, Rule, Examples1).                                     

remove( [Example | Examples], Rule, [Example | Examples1])  :-                         
   remove( Examples, Rule, Examples1).   

learn_conj( Rule, _, [], Vars, Rule, Vars ).                         

learn_conj( Rule, PosExamples,NegExamples, Vars, NewRule, RetVars)  :-
   choose_cond(Rule, PosExamples,NegExamples, Vars, Rule1, Vars1),                        
   filter( PosExamples, Rule1, PosExamples1),
   filter( NegExamples, Rule1, NegExamples1),
   learn_conj( Rule1, PosExamples1, NegExamples1, Vars1, NewRule, RetVars).

choose_cond(Rule, PosExamples, NegExamples, Vars, NewRule, RetVars)  :-
   findall( rule_pack(NR,NV)/Score, score( Rule, PosExamples, NegExamples, Vars, NR, NV, Score), RVs),
   best( RVs, rule_pack(NewRule, RetVars)).

best( [ AttVal/_], AttVal).
best( [ AV0/S0, AV1/S1 | AVSlist], AttVal)  :-
   S1  >  S0, !,                                               
   best( [AV1/S1 | AVSlist], AttVal)
   ;
   best( [AV0/S0 | AVSlist], AttVal).

score(Rule, PosExamples, NegExamples, Vars, NewRule, RetVars, Score) :-
   candidate( Rule, PosExamples, NegExamples, Vars, NewRule, RetVars),             
   filter( PosExamples, NewRule, Examples1),
   filter( NegExamples, NewRule, Examples2),
   length( Examples1, N1), 
   length( Examples2, N2),            
   N1 > 0,                                    
   Score is N1 - N2.

filter( Examples, Rule, Examples1)  :-
   findall(Example,(member( Example, Examples), covers(Rule, Example)),Examples1).

candidate(rule(Conseq, Anteced),PosExamples, NegExamples, Vars, rule(Conseq, [Expr|Anteced]), RetVars) :-
    build_expr(Vars, Expr, RetVars),
    suitable(rule(Conseq,[Expr|Anteced]), PosExamples, NegExamples).

build_expr(Vars, Expr, RetVars) :-
    predicate(Pred, N),
    build_arg_list(N, Vars, false, ArgList, RetVars),
    Expr =.. [Pred|ArgList].

build_arg_list(1, vars(New, Used, LocalUsed), true, [Arg], vars(RetNew, RetUsed, [])) :-
	insert_arg(vars(New, Used, LocalUsed), true, vars(RetNew, Used, RetLocal), _, Arg),
    conc(Used, RetLocal, RetUsed).

build_arg_list(1, vars(New, Used, LocalUsed), false, [Arg], vars(New, RetUsed, [])) :-
	member1(Arg,Used),
    not(member(Arg, LocalUsed)),
    conc(Used, LocalUsed, RetUsed).

build_arg_list(N, Vars, FlagIn, [Arg|RestArgs], RetVars) :-
    N > 1,
    insert_arg(Vars, FlagIn, Vars1, FlagOut, Arg),
    N1 is N -1,
    build_arg_list(N1, Vars1, FlagOut, RestArgs, RetVars).

insert_arg(vars(New, Used, LocalUsed), false, vars(New, Used, [Arg|LocalUsed]), true, Arg) :-
    member1(Arg, Used),
    not(member(Arg, LocalUsed)).

insert_arg(vars(New, Used, LocalUsed), true, vars(New1, Used, [Arg|LocalUsed]), true, Arg) :-
    member1(Arg, New),
    delete(Arg, New, New1).

insert_arg(vars(New, Used, LocalUsed), false, vars(New, Used, [Arg|LocalUsed]), false, Arg) :-
    member1(Arg, Used),
    not(member(Arg, LocalUsed)).

insert_arg(vars(New, Used, LocalUsed), true, vars(New1, Used, [Arg|LocalUsed]), false, Arg) :-
    member1(Arg, New),
    delete(Arg, New, New1).

suitable(rule(Conseq, Anteced), _, NegExamples):-
    member( Example, NegExamples),
    Example \= Conseq,
    not(covers(rule(Conseq, Anteced), Example)).

delete(X, [X|R], R).
delete(X, [Y|R], [Y|R1]) :-
    X \= Y,
    delete(X, R, R1).

member1(X, [X|_]).
member1(X, [_|Rest]) :-
    member1(X,Rest).

conc([], L2, L2).
conc([X|R1], L2, [X|RN]) :-
    conc(R1, L2, RN).

covers(rule(Conseq, Anteced), Example) :-
	match_conseq(Conseq, Example, Bindings),
	match_anteced(Anteced,Bindings,_).

match_conseq(Conseq, Example, BindingsOut) :-
    functor(Conseq,Functor,N),
	functor(Example,Functor,N),
	Conseq =.. [_|ArgList1],
	Example =.. [_|ArgList2],
	match_arg_lists(ArgList1,ArgList2,[],BindingsOut).

match_anteced([],Bindings,Bindings).

match_anteced([A|RestAnteced],BindingsIn,BindingsOut) :-
	match_expr(A,BindingsIn,Bindings1),
	match_anteced(RestAnteced,Bindings1,BindingsOut).

match_expr(Expr,BindingsIn,BindingsOut) :-
	known_fact(Fact),
	functor(Expr,Functor,N),
	functor(Fact,Functor,N),
	Expr =.. [_|ArgList1],
	Fact =.. [_|ArgList2],
	match_arg_lists(ArgList1,ArgList2,BindingsIn,BindingsOut).

match_arg_lists([],[],Bindings,Bindings).

match_arg_lists([Arg1|Rest1],[Arg2|Rest2],BindingsIn,BindingsOut) :-
	match_args(Arg1,Arg2,BindingsIn,Bindings1),
	match_arg_lists(Rest1,Rest2,Bindings1,BindingsOut).

match_args(Arg1, Arg2, BindingsIn, [NewBinding|BindingsIn]):-
           find_binding(Arg1, Arg2, BindingsIn, NewBinding).

match_args(Arg1, Arg2, BindingsIn, BindingsIn):-
           find_binding(Arg1, Arg2, BindingsIn, []).

find_binding(Arg1, Arg2, [binding(Arg1, Arg2) | _], []):- 
    !.
find_binding(Arg1, Arg2, [binding(X, _) | RestBindings], BindingOut) :-
    Arg1 \= X,
    find_binding(Arg1, Arg2, RestBindings, BindingOut).
find_binding(Arg1, Arg2, [], binding(Arg1, Arg2)).
