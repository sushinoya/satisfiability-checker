:- use_module(library(lists)).
:- use_module(library(ordset)).

% Definitions of true and false
top.
bot :- fail.

% The negate procedure
negate(not(A), A) :- !.
negate(A, not(A)).



% FOR CONVEINIENT LIST PROCEDURES

% append_to_all(List, ListOfLists) appends List to every single element of the ListOfLists.
append_to_all(_, [], []).
append_to_all(List, [H|T], [Res1|MoreRes]) :- 
		append(List, H, Res1), 
		append_to_all(List, T, MoreRes).

% remove_from_all(Elem, ListOfLists) removes Elem from every list in ListOfLists
remove_from_all(_, [], []).
remove_from_all(Elem, [List|OtherLists], Result) :-
		remove(Elem, List, FilteredList),
		remove_from_all(Elem, OtherLists, MoreResults),
		Result = [FilteredList|MoreResults].

% delete/3 does not well with []. Remove is a simple implementation of delete/3
% which does not have [] issues.
remove(_, [], []).
remove(H, [H|T], FilteredList) :- !, remove(H, T, FilteredList).
remove(Elem, [H|T], [H|FilteredList]) :- remove(Elem, T, FilteredList).

% Test Cases
% remove_from_all(a, [[a], [a,b,c], [s,a,d,a,d], []], X).
% append_to_all([44], [[1,2,3], [], [1,2]], Res).



% PROCEDURE TO GET ALL LITERALS 

% Gets a list of all the literals in the clauses
all_literals(Clauses, Literals) :- 
		positive_and_negative_literals(Clauses, PosAndNegLits),
		unsigned_literals(PosAndNegLits, UnsignedLiterals), % Removes negations like - not a
		sort(UnsignedLiterals, Literals). % Removes Duplicates
		
% unsigned_literals(PosAndNegLits, Literals)
unsigned_literals([], []).
unsigned_literals([not(A)|T], [A|Literals]) :- !, unsigned_literals(T, Literals).
unsigned_literals([A|T], [A|Literals]) :- !, unsigned_literals(T, Literals).


positive_and_negative_literals(Clauses, PosAndNegLits) :-
		flatten(Clauses, RepeatedLiterals), 
		sort(RepeatedLiterals, PosAndNegLits). % Removes Duplicates

% Test Cases
% all_literals([[a], [a,b,c], [], [not(k), not(f)]], X).



% MAIN RESOLUTION PROCEDURES

% For a given literal l, split clauses into three sets (which are represented by lists):
% 1. Clauses which contain l
% 2. Clauses which contain negation of l
% 3. Clauses which don't contain l or the negation of l
separate_clauses(_, [], [], [], []).
separate_clauses(Lit, [Clause|MoreClauses], [Clause|PosClauses], NegClauses, NeitherClauses) :-
	member(Lit, Clause), negate(Lit, NegLit), \+ member(NegLit, Clause), !,
	separate_clauses(Lit, MoreClauses, PosClauses, NegClauses, NeitherClauses).
separate_clauses(Lit, [Clause|MoreClauses], PosClauses, [Clause|NegClauses], NeitherClauses) :-
	\+ member(Lit, Clause), negate(Lit, NegLit), member(NegLit, Clause), !,
	separate_clauses(Lit, MoreClauses, PosClauses, NegClauses, NeitherClauses).
separate_clauses(Lit, [Clause|MoreClauses], PosClauses, NegClauses, [Clause|NeitherClauses]) :-
	!, separate_clauses(Lit, MoreClauses, PosClauses, NegClauses, NeitherClauses).

% Test Cases
% separate_clauses(x1, [[x2, x3], [x1, x2, not(x3)], [x2, not(x1)], [x1, not(x2), not(x3)]], X, Y, Z).
% separate_clauses(x1, [[x1], [x2], [not(x1)]], X, Y, Z).
% separate_clauses(a, [[a, b], [not(a), c]], PosClauses, NegClauses, NeitherClauses).


% resolve_separated_clause(Lit, PosClauses, NegClauses, CombinedClauses)
% This procedure is the main resolution procedure which removes the positive
% literal Lit from a clause and its negation from another clause and joins them
% to make a new clause. It goes through all clauses which contain positive Lit and
% negated Lit.
resolve_separated_clauses(_, PosClauses, [], PosClauses).
resolve_separated_clauses(_, [], NegClauses, NegClauses).
resolve_separated_clauses(Lit, [PosClause|PosClauses], NegClauses, Result) :-
    remove(Lit, PosClause, FilteredPosClause),
    negate(Lit, NegLit), remove_from_all(NegLit, NegClauses, FilteredNegClauses),
    append_to_all(FilteredPosClause, FilteredNegClauses, CombinedClauses),
    resolve_separated_clauses(Lit, PosClauses, NegClauses, MoreCombinedClauses),
    append(CombinedClauses, MoreCombinedClauses, Result).

% Test Cases
% resolve_separated_clauses(x1, [[x1, x2, not x3], [x1, not x2, not x3]], [[x2, not x1]], Res).



% CLAUSE REFINEMENTS

% Superset Elimination
is_superset_of_a_elem(_, []) :- fail.
is_superset_of_a_elem(X, [H|_]) :- 
    ord_subset(H, X), !.
is_superset_of_a_elem(X, [H|T]) :- 
    \+ ord_subset(H, X), is_superset_of_a_elem(X, T).


eliminate_superset_clauses_in_one_direction([L|[]], [L]).
eliminate_superset_clauses_in_one_direction([Clause|Clauses], FilteredClauses) :-
	is_superset_of_a_elem(Clause, Clauses), !,
	eliminate_superset_clauses_in_one_direction(Clauses, FilteredClauses).
eliminate_superset_clauses_in_one_direction([Clause|Clauses], [Clause|FilteredClauses]) :-
	\+ is_superset_of_a_elem(Clause, Clauses),
	eliminate_superset_clauses_in_one_direction(Clauses, FilteredClauses).


eliminate_superset_clauses(Clauses, FilteredClauses) :-
    eliminate_superset_clauses_in_one_direction(Clauses, OnePassClauses),
    reverse(OnePassClauses, ReversedClauses),
    eliminate_superset_clauses_in_one_direction(ReversedClauses, FilteredClauses).

% Test Cases
%  eliminate_superset_clauses([[a,b,c], [a,b,c,d], [], [r, j], [r, j, k]], X).


% Duplicate Literal Elimination
elimiate_duplicate_literals_in_clauses([], []).
elimiate_duplicate_literals_in_clauses([Clause|Clauses], NoDupClauses) :-
    sort(Clause, ClauseWithoutDuplicates),
    elimiate_duplicate_literals_in_clauses(Clauses, OtherFilteredClauses),
    NoDupClauses = [ClauseWithoutDuplicates|OtherFilteredClauses].

% Duplicate Clause Elimination - works because Duplicate Literal Elimination sorts the clauses
eliminate_duplicate_clauses([], []).
eliminate_duplicate_clauses(Clauses, NoDupClauses) :-
    sort(Clauses, NoDupClauses).


% Tautology Elimination - Remove clauses with A and not(A) in them.
% [Clause|OtherClauses] is a list of all clauses, NonTrivialClauses is a list of non-trivial clauses in [Clause|OtherClauses]
eliminate_trivial_clauses([], []).
eliminate_trivial_clauses([Clause|OtherClauses], NonTrivialClauses) :- 
    member(Lit, Clause), 
    negate(Lit, NLit), 
    member(NLit, Clause), !, 
    eliminate_trivial_clauses(OtherClauses, NonTrivialClauses).
eliminate_trivial_clauses([Clause|OtherClauses], [Clause|NonTrivialClauses]) :- 
    eliminate_trivial_clauses(OtherClauses, NonTrivialClauses).

% Test Cases
% eliminate_trivial_clauses([[a, not a], [b], [a, b, c, not c], [d]], X).


% Pure Literal Elimination

pure_literals([], []).
pure_literals(Clauses, PureLiterals) :-
    positive_and_negative_literals(Clauses, Literals),
    filter_pure_literals(Literals, PureLiterals).


filter_pure_literals([], []).
filter_pure_literals([Lit|Literals], [Lit|PureLiterals]) :-
    negate(Lit, NegLit), \+ member(NegLit, Literals), !,
    filter_pure_literals(Literals, PureLiterals).
filter_pure_literals([Lit|Literals], PureLiterals) :-
    negate(Lit, NegLit), 
    remove(Lit, Literals, FilteredLiteralsIntermediate),
    remove(NegLit, FilteredLiteralsIntermediate, FilteredLiterals),
    filter_pure_literals(FilteredLiterals, PureLiterals).


remove_clauses_containing_literal(_, [], []).
remove_clauses_containing_literal(Lit, [Clause|Clauses], FilteredClauses) :-
    member(Lit, Clause), !, remove_clauses_containing_literal(Lit, Clauses, FilteredClauses).
remove_clauses_containing_literal(Lit, [Clause|Clauses], [Clause|FilteredClauses]) :-
    remove_clauses_containing_literal(Lit, Clauses, FilteredClauses).


remove_literal_from_clauses(_, [], []).
remove_literal_from_clauses(Lit, [Clause|Clauses], [FilteredClause|FilteredClauses]) :-
    remove(Lit, Clause, FilteredClause), remove_literal_from_clauses(Lit, Clauses, FilteredClauses).


unit_propogate(_, [], []).
unit_propogate(Lit, Clauses, FilteredClauses) :-
    negate(Lit, NegLit),
    remove_clauses_containing_literal(Lit, Clauses, FilteredClausesIntermediate),
    remove_literal_from_clauses(NegLit, FilteredClausesIntermediate, FilteredClauses).


eliminate_literals([], Clauses, Clauses).
eliminate_literals([Lit|PureLiterals], Clauses, FilteredClauses) :-
    unit_propogate(Lit, Clauses, OnceFilteredClauses),
    eliminate_literals(PureLiterals, OnceFilteredClauses, FilteredClauses).

eliminate_pure_literals(Clauses, FilteredClauses) :-
    pure_literals(Clauses, PureLiterals),
    eliminate_literals(PureLiterals, Clauses, FilteredClauses).

% Test Cases
% pure_literals([[a], [a, not b, c], [b, not c], [d, a], [not e]], X).
% remove_literal_from_clauses(a, [[a], [a, not b, c], [b, not c], [d, a]], X).
% remove_clauses_containing_literal(a, [[a], [a, not b, c], [b, not c], [d, a]], X).
% eliminate_literals([a], [[a], [a, not b, c], [b, not c], [d, a]], X).
% unit_propogate(d, [[b], [a, not b, c], [b, not c], [d, a], [not d, f]], X).
% eliminate_literals([d], [[b], [a, not b, c], [b, not c], [d, a], [not d, f]], X).
% eliminate_pure_literals([[a], [a, not b, c], [b, not c], [d, a]], X).


% single lit elim



% Refines Clauses using all the refinements above
refine_clauses([], []).
refine_clauses(Clauses, ImprovedClauses) :-
    elimiate_duplicate_literals_in_clauses(Clauses, NoDupLitClauses),
    eliminate_duplicate_clauses(NoDupLitClauses, NoDupClauses),
    eliminate_trivial_clauses(NoDupClauses, NonTrivialClauses),
    ImprovedClauses = NonTrivialClauses.




% MAIN DRIVER CODE

dp([[]]) :- !.
dp(Clauses) :-
	all_literals(Clauses, Literals),
	dp_helper(Clauses, Literals, FinalClauses),
	\+ member([], FinalClauses), !.

dp_helper([], _, []).
dp_helper(Clauses, [], Clauses).
dp_helper(Clauses, [Lit|OtherLit], OtherResolvants) :-
    refine_clauses(Clauses, ImprovedClauses),
    separate_clauses(Lit, ImprovedClauses, PosClauses, NegClauses, NeitherClauses),
    resolve_separated_clauses(Lit, PosClauses, NegClauses, Resolvents),
    \+ member([], Resolvents), % Prune early if empty clause is found
    append(Resolvents, NeitherClauses, UpdatedClauses),
    dp_helper(UpdatedClauses, OtherLit, OtherResolvants).

% Test Cases
% dp_helper([[a, b], [not(a), c]], [a,b,c], X).
% dp_helper([[a], [not(a)], [b, c], [not(c), not(b)]], [a,b,c], X).

% dp([]).
% dp([[]]).
% dp([[a], [not a]]).
% dp([[a], [not a, b]]).
% dp([[a], [not a, b], [not b]]).
% dp([[a], [not a, b], [not b, not c], [c]]).
% dp([[a], [not a, b], [not b, not c], [c, d]]).