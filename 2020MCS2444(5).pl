%(** ASSIGNMENT 6 : SUBMITTED BY : AAYUSH KUMAR SINGH 2020MCS2444)

% Variables using constructor v().
% abstractions using constructor abs( , ) 1st argument is variable
% and second is expression
% applications: app( , ) where both the arguments are expressions.

%base types t_int, t_bool.
% function types (T1 -> T2) represented using const arrow(T1, T2).
lookup(_, [ ], _) :- fail.
lookup( X, [ (X,V) | _], V) :- !.
lookup(X,[ _ | R], V) :- lookup(X,R, V).

hastype(Gamma, v(X), T) :- lookup(X, Gamma, T).
%plus
hastype(Gamma, plus(E1,E2), t_int):- hastype(Gamma, E1, t_int), hastype(Gamma, E2, t_int).
%times
hastype(Gamma, times(E1, E2), t_int):- hastype(Gamma, E1, t_int), hastype(Gamma, E2, t_int).

%negation
hastype(Gamma, neg(E), t_bool):- hastype(Gamma, E, t_bool).
%Conjuntion
hastype(Gamma, conj(E1, E2), t_bool):- hastype(Gamma, E1, t_bool), hastype(Gamma, E2, t_bool).
%Disjunction
hastype(Gamma, disj(E1, E2), t_bool):- hastype(Gamma, E1, t_bool), hastype(Gamma, E2, t_bool).

%comparision Operators
%less than equal
hastype(Gamma, leq(E1, E2), t_bool):- hastype(Gamma, E1, t_int), hastype(Gamma, E2, t_int).
%equal
hastype(Gamma, equals(E1, E2), t_bool):- hastype(Gamma, E1, t_int), hastype(Gamma, E2, t_int).
%geq
hastype(Gamma, geq(E1, E2), t_bool):- hastype(Gamma, E1, t_int), hastype(Gamma, E2, t_int).

%unit
hastype(Gamma, unit, t_unit).

%pair expression of form
hastype(Gamma, pair(E1, E2), product(T1, T2)):- hastype(Gamma, E1, T1), hastype(Gamma, E2, T2).

%project expressions
hastype(Gamma, proj1(E), T1):- hastype(Gamma, E, prod(T1, _)).
hastype(Gamma, proj2(E), T2):- hastype(Gamma, E, prod(_, T2)).

%injection expressions
hastype(Gamma, inl(E), sum(T1, _)):- hastype(Gamma, E, T1).
hastype(Gamma, inr(E), sum(_, T2)):- hastype(Gamma, E, T2).

%case expressions
hastype(Gamma, case(E0, inl(X), E1, inr(Y), E2), T):- hastype(Gamma, E0, sum(T1, T2)), hastype([(X,T1)|Gamma], E1, T), hastype([(Y, T2)|Gamma], E2, T).

%conditional expression
hastype(Gamma, ifte(E0, E1, E2), T):- hastype(Gamma, E0, t_bool), hastype(Gamma, E1, T), hastype(Gamma, E2, T).

Examples:
%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_int)], plus(v(x), v(u)), T).
%t_int.
%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_int)], plus(times(v(z), v(w)), v(u)), T).
%False.


%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], disj(conj(v(y), v(z)), neg(v(w))), T).
%t_bool.
%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], disj(conj(v(y), v(z)), v(x)), T).
%False.

%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], geq(v(u), v(x)), T).
%t_bool.

%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], pair(v(u), v(x)), T).
%T = product(t_int,t_int).

%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], proj(v(x)), t_int).

%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], inl(v(x)),sum(T, _)).
%T =  t_int
%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], inr(v(z)),sum(_, T)).
%T = t_bool

%hastype([(u, t_int), (x, t_int), (y, t_bool), (z, t_bool), (w, t_bool)], ifte(equals(v(u), v(x)), v(y), v(z)), T).


