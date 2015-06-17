predicate(brat,2).
predicate(maz,2).

candidate(rule(Conseq, Anteced), Vars, rule(Conseq, [Expr|Anteced]), RetVars) :-
    build_expr(Vars, Expr, RetVars).
    %suitable(rule(Conseq,[Expr|Anteced]), PosExamples, NegExamples)

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