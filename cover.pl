covers(rule(Conseq, Anteced), Example) :-
	match_conseq(Conseq, Example, Bindings),
	match_anteced(Anteced,Bindings,BindingsOut).

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

match_args(Arg1, Arg2, BindingsIn, BindingsIn):-
    findNewBinding(Arg1, Arg2, BindingsIn, []).
match_args(Arg1, Arg2, BindingsIn, [NewBinding | BindingsIn]):-
    findNewBinding(Arg1, Arg2, BindingsIn, NewBinding).

findNewBinding(Arg1, Arg2, [], binding(Arg1, Arg2)).
findNewBinding(Arg1, Arg2, [binding(X,_)|RestBindings], NewBinding):-
    Arg1 \= X, !,
    findNewBinding(Arg1, Arg2, RestBindings, NewBinding).
findNewBinding(Arg1, _, [binding(Arg1, _)|_], []).

             