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

make_first_list_same_size([H1|[]], [H2|[]], [H1]).
make_first_list_same_size([H1|[]], [H2|T1], [H1|Res]) :-
    make_first_list_same_size([H1|[]], T1, Res), !.
make_first_list_same_size([H1|T1], [H2|T2], [H1|Res]) :-
    make_first_list_same_size(T1, T2, Res).

% Extends the shorter list to make it of the same length as the other list
same_size(List1, List2, List1Extended, List2) :-
    length(List1, L1), length(List2, L2), L1 < L2, !, 
    make_first_list_same_size(List1, List2, List1Extended).
same_size(List1, List2, List1, List2Extended) :-
    make_first_list_same_size(List2, List1, List2Extended).


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
% resolve_separated_clauses(_, PosClauses, [], PosClauses).
% resolve_separated_clauses(_, [], NegClauses, NegClauses).
% resolve_separated_clauses(Lit, [PosClause|PosClauses], NegClauses, Result) :-
%     remove(Lit, PosClause, FilteredPosClause),
%     negate(Lit, NegLit), remove_from_all(NegLit, NegClauses, FilteredNegClauses),
%     append_to_all(FilteredPosClause, FilteredNegClauses, CombinedClauses),
%     resolve_separated_clauses(Lit, PosClauses, NegClauses, MoreCombinedClauses),
%     append(CombinedClauses, MoreCombinedClauses, ResultWithDuplicates),
%     sort(ResultWithDuplicates, Result).
    % writeln(Result).

resolve_separated_clauses(_, PosClauses, [], PosClauses) :- !.
resolve_separated_clauses(_, [], NegClauses, NegClauses) :- !.

resolve_separated_clauses(Lit, PosClauses, NegClauses, Result) :-
    % write("Called resolve_separated_clauses("), write(Lit), write(", "), write(PosClauses), write(", "), write(NegClauses), writeln(", Res)..."),
    length(PosClauses, PL), length(NegClauses, NL), \+ PL == NL,
    same_size(PosClauses, NegClauses, PaddedPosClauses, PaddedNegClauses), !,
    resolve_separated_clauses(Lit, PaddedPosClauses, PaddedNegClauses, Result).

resolve_separated_clauses(Lit, [PosClause|PosClauses], [NegClause|NegClauses], Result) :-
    negate(Lit, NegLit),
    remove(Lit, PosClause, FilteredPosClause),
    remove(NegLit, NegClause, FilteredNegClause),
    append(FilteredPosClause, FilteredNegClause, CombinedClause),
    resolve_separated_clauses(Lit, PosClauses, NegClauses, MoreCombinedClauses),
    Result = [CombinedClause|MoreCombinedClauses].


% Test Cases
% resolve_separated_clauses(a, [[a]], [[not a, b]], X).
% resolve_separated_clauses(x1, [[x1, x2, not x3], [x1, not x2, not x3]], [[x2, not x1]], Res).
% resolve_separated_clauses(x1, [[x1], [x1, not x2, not x3]], [[x3, not x1]], Res).
% resolve_separated_clauses(x1, [[x1], [x1, not x2, not x3]], [[x3, not x1], [x4, not x1], [x5, not x1]], Res).

% CLAUSE REFINEMENTS

% Superset Elimination
% is_superset_of_a_elem(_, []) :- fail.
% is_superset_of_a_elem(X, [H|_]) :- 
%     ord_subset(H, X), !.
% is_superset_of_a_elem(X, [H|T]) :- 
%     \+ ord_subset(H, X), is_superset_of_a_elem(X, T).


% eliminate_superset_clauses_in_one_direction([L|[]], [L]).
% eliminate_superset_clauses_in_one_direction([Clause|Clauses], FilteredClauses) :-
% 	is_superset_of_a_elem(Clause, Clauses), !,
% 	eliminate_superset_clauses_in_one_direction(Clauses, FilteredClauses).
% eliminate_superset_clauses_in_one_direction([Clause|Clauses], [Clause|FilteredClauses]) :-
% 	\+ is_superset_of_a_elem(Clause, Clauses),
% 	eliminate_superset_clauses_in_one_direction(Clauses, FilteredClauses).


% eliminate_superset_clauses(Clauses, FilteredClauses) :-
%     eliminate_superset_clauses_in_one_direction(Clauses, OnePassClauses),
%     reverse(OnePassClauses, ReversedClauses),
%     eliminate_superset_clauses_in_one_direction(ReversedClauses, FilteredClauses).

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


unit_propogate_for_literals([], Clauses, Clauses).
unit_propogate_for_literals([Lit|PureLiterals], Clauses, FilteredClauses) :-
    unit_propogate(Lit, Clauses, OnceFilteredClauses),
    unit_propogate_for_literals(PureLiterals, OnceFilteredClauses, FilteredClauses).

eliminate_pure_literals(Clauses, FilteredClauses) :-
    pure_literals(Clauses, PureLiterals),
    unit_propogate_for_literals(PureLiterals, Clauses, FilteredClauses).

% Test Cases
% pure_literals([[a], [a, not b, c], [b, not c], [d, a], [not e]], X).
% remove_literal_from_clauses(a, [[a], [a, not b, c], [b, not c], [d, a]], X).
% remove_clauses_containing_literal(a, [[a], [a, not b, c], [b, not c], [d, a]], X).
% unit_propogate_for_literals([a], [[a], [a, not b, c], [b, not c], [d, a]], X).
% unit_propogate(d, [[b], [a, not b, c], [b, not c], [d, a], [not d, f]], X).
% unit_propogate_for_literals([d], [[b], [a, not b, c], [b, not c], [d, a], [not d, f]], X).
% eliminate_pure_literals([[a], [a, not b, c], [b, not c], [d, a]], X).




% Refines Clauses using all the refinements above
refine_clauses([], []).
refine_clauses(Clauses, ImprovedClauses) :-
    elimiate_duplicate_literals_in_clauses(Clauses, NoDupLitClauses),
    eliminate_duplicate_clauses(NoDupLitClauses, NoDupClauses),
    eliminate_trivial_clauses(NoDupClauses, NonTrivialClauses),
    ImprovedClauses = NonTrivialClauses.

refine_and_eliminate_pure_literals(Clauses, ImprovedClauses) :-
    eliminate_pure_literals(Clauses, ClausesWithoutPureLiterals),
    refine_clauses(ClausesWithoutPureLiterals, ImprovedClauses).



% MAIN DP DRIVER CODE

dp([[]]) :- fail, !.
dp(Clauses) :-
	all_literals(Clauses, Literals),
	dp_helper(Clauses, Literals, FinalClauses),
	\+ member([], FinalClauses), !.

dp_helper([], _, []).
dp_helper(Clauses, [], Clauses).
dp_helper(Clauses, [Lit|OtherLit], OtherResolvants) :-
    \+ member([], Clauses), % Prune early if empty clause is found
    refine_and_eliminate_pure_literals(Clauses, ImprovedClauses),
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

is_unit_clause(Clause) :- Clause = [_].

unit_clauses([], []).
unit_clauses([Clause|Clauses], [Clause|UnitClauses]) :- 
    is_unit_clause(Clause), !,
    unit_clauses(Clauses, UnitClauses).
unit_clauses([Clause|Clauses], UnitClauses) :- 
    \+ is_unit_clause(Clause),
    unit_clauses(Clauses, UnitClauses).

unit_clause_literals(Clause, UnitClauseLiterals) :-
    unit_clauses(Clause, UnitClauses),
    flatten(UnitClauses, UnitClauseLiteralsWithDuplicates),
    sort(UnitClauseLiteralsWithDuplicates, UnitClauseLiterals).

% unit_clauses([[b], [a, not b, c], [b, not c], [d, a], [not d, f], [not f]], X).
% unit_clause_literals([[b], [a, not b, c], [b, not c], [d, a], [not d, f], [not f]], X).

% MAIN DLL DRIVER CODE
dll(Clauses) :-
    \+ member([], Clauses),
    all_literals(Clauses, Literals),
    dll_helper(Literals, Clauses).

dll_helper(_, []). % Clauses is empty cube
dll_helper([Lit|Literals], Clauses) :-
    \+ member([], Clauses), % Clauses contain empty clause
    negate(Lit, NegLit),
    unit_clause_literals(Clauses, UnitClauseLiterals),
    unit_propogate_for_literals(UnitClauseLiterals, Clauses, UpdatedClauses),
    union([[Lit]], UpdatedClauses, ClausesWithPosLit),
    union([[NegLit]], UpdatedClauses, ClausesWithNegLit),
    append(Literals, [Lit], UpdatedLiterals),
    execute_or(
        UpdatedClauses = [], 
        dll_helper(UpdatedLiterals, ClausesWithPosLit), 
        dll_helper(UpdatedLiterals, ClausesWithNegLit)
    ).

execute_or(A, _, _) :- A, !.
execute_or(_, B, _) :- B, !.
execute_or(_, _, C) :- C, !.


% dll([]).
% dll([[]]).
% dll([[a], [not a]]).
% dll([[a], [not a, b]]).
% dll([[a], [not a, b], [not b]]).
% dll([[a], [not a, b], [not b, not c], [c]]).
% dll([[a], [not a, b], [not b, not c], [c, d]]).

sat_dp1 :- dp([[a10, a9, not(a6)], [a8, a19, a10], [a1, a18, a13], [not(a20), a18, a8], [a12, a18, a15], [a19, not(a14), not(a5)], [not(a3), not(a2), not(a17)], [a10, not(a9), a18], [not(a4), not(a17), a3], [not(a20), not(a5), not(a3)], [a17, not(a13), not(a4)], [a14, not(a1), a19], [a7, a3, not(a18)], [not(a9), not(a8), a12], [not(a17), not(a19), a10], [not(a10), not(a11), not(a17)], [a10, not(a5), a15], [not(a17), a2, not(a10)], [not(a9), a14, not(a1)], [not(a4), not(a1), not(a19)], [not(a17), a9, not(a3)], [a8, not(a11), not(a19)], [not(a9), a14, not(a15)], [not(a11), not(a16), not(a12)], [a11, not(a19), not(a17)], [a2, a9, a5], [not(a18), not(a9), not(a17)], [a9, not(a19), not(a8)], [not(a2), not(a6), a10], [a10, not(a8), not(a2)], [a2, a19, not(a6)], [not(a20), a12, a8], [a4, not(a1), a9], [a9, not(a2), not(a14)], [not(a11), a7, not(a20)], [a17, a3, not(a14)], [a15, not(a5), not(a9)], [not(a4), a12, not(a13)], [a19, a9, a10], [a11, not(a13), not(a6)], [a4, a20, a12], [a20, a9, a18], [not(a6), a12, a20], [a14, a1, a15], [not(a9), not(a12), not(a15)], [a12, a1, not(a11)], [a12, a6, not(a3)], [not(a18), a13, a3], [a4, a6, not(a19)], [not(a14), a18, not(a8)], [a16, a15, not(a2)], [not(a8), a12, not(a2)], [not(a8), a5, not(a16)], [a1, a15, not(a18)], [a20, not(a19), not(a11)], [not(a6), not(a10), a8], [not(a18), not(a11), a2], [not(a1), a18, not(a17)], [a19, a2, a13], [not(a5), not(a2), not(a20)], [not(a18), a5, a6], [a13, a15, a8], [a6, not(a5), not(a4)], [a3, not(a14), a12], [a11, not(a18), not(a1)], [a1, not(a19), a20], [not(a11), not(a7), a18], [a6, a18, a9], [not(a9), not(a4), a14], [a1, a7, not(a2)], [a4, not(a19), not(a17)], [not(a20), not(a19), a18], [not(a2), a8, not(a11)], [not(a19), a13, not(a4)], [a20, a4, a1], [not(a18), not(a11), not(a20)], [not(a15), not(a19), not(a10)], [a14, a17, not(a8)], [not(a15), a7, not(a9)], [not(a12), a5, a15], [not(a12), not(a3), not(a13)], [not(a2), a12, a11], [not(a11), not(a16), a3], [not(a14), a17, not(a3)], [not(a4), not(a6), a8], [not(a7), not(a14), not(a2)], [not(a19), a2, a4], [not(a1), not(a20), a11], [not(a12), a13, not(a18)], [a8, not(a4), a16], [not(a9), a6, a19]]).
sat_dll1 :- dll([[a10, a9, not(a6)], [a8, a19, a10], [a1, a18, a13], [not(a20), a18, a8], [a12, a18, a15], [a19, not(a14), not(a5)], [not(a3), not(a2), not(a17)], [a10, not(a9), a18], [not(a4), not(a17), a3], [not(a20), not(a5), not(a3)], [a17, not(a13), not(a4)], [a14, not(a1), a19], [a7, a3, not(a18)], [not(a9), not(a8), a12], [not(a17), not(a19), a10], [not(a10), not(a11), not(a17)], [a10, not(a5), a15], [not(a17), a2, not(a10)], [not(a9), a14, not(a1)], [not(a4), not(a1), not(a19)], [not(a17), a9, not(a3)], [a8, not(a11), not(a19)], [not(a9), a14, not(a15)], [not(a11), not(a16), not(a12)], [a11, not(a19), not(a17)], [a2, a9, a5], [not(a18), not(a9), not(a17)], [a9, not(a19), not(a8)], [not(a2), not(a6), a10], [a10, not(a8), not(a2)], [a2, a19, not(a6)], [not(a20), a12, a8], [a4, not(a1), a9], [a9, not(a2), not(a14)], [not(a11), a7, not(a20)], [a17, a3, not(a14)], [a15, not(a5), not(a9)], [not(a4), a12, not(a13)], [a19, a9, a10], [a11, not(a13), not(a6)], [a4, a20, a12], [a20, a9, a18], [not(a6), a12, a20], [a14, a1, a15], [not(a9), not(a12), not(a15)], [a12, a1, not(a11)], [a12, a6, not(a3)], [not(a18), a13, a3], [a4, a6, not(a19)], [not(a14), a18, not(a8)], [a16, a15, not(a2)], [not(a8), a12, not(a2)], [not(a8), a5, not(a16)], [a1, a15, not(a18)], [a20, not(a19), not(a11)], [not(a6), not(a10), a8], [not(a18), not(a11), a2], [not(a1), a18, not(a17)], [a19, a2, a13], [not(a5), not(a2), not(a20)], [not(a18), a5, a6], [a13, a15, a8], [a6, not(a5), not(a4)], [a3, not(a14), a12], [a11, not(a18), not(a1)], [a1, not(a19), a20], [not(a11), not(a7), a18], [a6, a18, a9], [not(a9), not(a4), a14], [a1, a7, not(a2)], [a4, not(a19), not(a17)], [not(a20), not(a19), a18], [not(a2), a8, not(a11)], [not(a19), a13, not(a4)], [a20, a4, a1], [not(a18), not(a11), not(a20)], [not(a15), not(a19), not(a10)], [a14, a17, not(a8)], [not(a15), a7, not(a9)], [not(a12), a5, a15], [not(a12), not(a3), not(a13)], [not(a2), a12, a11], [not(a11), not(a16), a3], [not(a14), a17, not(a3)], [not(a4), not(a6), a8], [not(a7), not(a14), not(a2)], [not(a19), a2, a4], [not(a1), not(a20), a11], [not(a12), a13, not(a18)], [a8, not(a4), a16], [not(a9), a6, a19]]).

sat_dp2 :-dp([[a4, not(a18), a19], [a3, a18, not(a5)], [not(a5), not(a8), not(a15)], [not(a20), a7, not(a16)], [a10, not(a13), not(a7)], [not(a12), not(a9), a17], [a17, a19, a5], [not(a16), a9, a15], [a11, not(a5), not(a14)], [a18, not(a10), a13], [not(a3), a11, a12], [not(a6), not(a17), not(a8)], [not(a18), a14, a1], [not(a19), not(a15), a10], [a12, a18, not(a19)], [not(a8), a4, a7], [not(a8), not(a9), a4], [a7, a17, not(a15)], [a12, not(a7), not(a14)], [not(a10), not(a11), a8], [a2, not(a15), not(a11)], [a9, a6, a1], [not(a11), a20, not(a17)], [a9, not(a15), a13], [a12, not(a7), not(a17)], [not(a18), not(a2), a20], [a20, a12, a4], [a19, a11, a14], [not(a16), a18, not(a4)], [not(a1), not(a17), not(a19)], [not(a13), a15, a10], [not(a12), not(a14), not(a13)], [a12, not(a14), not(a7)], [not(a7), a16, a10], [a6, a10, a7], [a20, a14, not(a16)], [not(a19), a17, a11], [not(a7), a1, not(a20)], [not(a5), a12, a15], [not(a4), not(a9), not(a13)], [a12, not(a11), not(a7)], [not(a5), a19, not(a8)], [a1, a16, a17], [a20, not(a14), not(a15)], [a13, not(a4), a10], [a14, a7, a10], [not(a5), a9, a20], [a10, a1, not(a19)], [not(a16), not(a15), not(a1)], [a16, a3, not(a11)], [not(a15), not(a10), a4], [a4, not(a15), not(a3)], [not(a10), not(a16), a11], [not(a8), a12, not(a5)], [a14, not(a6), a12], [a1, a6, a11], [not(a13), not(a5), not(a1)], [not(a7), not(a2), a12], [a1, not(a20), a19], [not(a2), not(a13), not(a8)], [a15, a18, a4], [not(a11), a14, a9], [not(a6), not(a15), not(a2)], [a5, not(a12), not(a15)], [not(a6), a17, a5], [not(a13), a5, not(a19)], [a20, not(a1), a14], [a9, not(a17), a15], [not(a5), a19, not(a18)], [not(a12), a8, not(a10)], [not(a18), a14, not(a4)], [a15, not(a9), a13], [a9, not(a5), not(a1)], [a10, not(a19), not(a14)], [a20, a9, a4], [not(a9), not(a2), a19], [not(a5), a13, not(a17)], [a2, not(a10), not(a18)], [not(a18), a3, a11], [a7, not(a9), a17], [not(a15), not(a6), not(a3)], [not(a2), a3, not(a13)], [a12, a3, not(a2)], [not(a2), not(a3), a17], [a20, not(a15), not(a16)], [not(a5), not(a17), not(a19)], [not(a20), not(a18), a11], [not(a9), a1, not(a5)], [not(a19), a9, a17], [a12, not(a2), a17], [a4, not(a16), not(a5)]]).
sat_dll2 :- dll([[a4, not(a18), 19], [a3, a18, not(a5)], [not(a5), not(a8), not(a15)], [not(a20), a7, not(a16)], [a10, not(a13), not(a7)], [not(a12), not(a9), a17], [a17, a19, a5], [not(a16), a9, a15], [a11, not(a5), not(a14)], [a18, not(a10), a13], [not(a3), a11, a12], [not(a6), not(a17), not(a8)], [not(a18), a14, a1], [not(a19), not(a15), a10], [a12, a18, not(a19)], [not(a8), a4, a7], [not(a8), not(a9), a4], [a7, a17, not(a15)], [a12, not(a7), not(a14)], [not(a10), not(a11), a8], [a2, not(a15), not(a11)], [a9, a6, a1], [not(a11), a20, not(a17)], [a9, not(a15), a13], [a12, not(a7), not(a17)], [not(a18), not(a2), a20], [a20, a12, a4], [a19, a11, a14], [not(a16), a18, not(a4)], [not(a1), not(a17), not(a19)], [not(a13), a15, a10], [not(a12), not(a14), not(a13)], [a12, not(a14), not(a7)], [not(a7), a16, a10], [a6, a10, a7], [a20, a14, not(a16)], [not(a19), a17, a11], [not(a7), a1, not(a20)], [not(a5), a12, a15], [not(a4), not(a9), not(a13)], [a12, not(a11), not(a7)], [not(a5), a19, not(a8)], [a1, a16, a17], [a20, not(a14), not(a15)], [a13, not(a4), a10], [a14, a7, a10], [not(a5), a9, a20], [a10, a1, not(a19)], [not(a16), not(a15), not(a1)], [a16, a3, not(a11)], [not(a15), not(a10), a4], [a4, not(a15), not(a3)], [not(a10), not(a16), a11], [not(a8), a12, not(a5)], [a14, not(a6), a12], [a1, a6, a11], [not(a13), not(a5), not(a1)], [not(a7), not(a2), a12], [a1, not(a20), a19], [not(a2), not(a13), not(a8)], [a15, a18, a4], [not(a11), a14, a9], [not(a6), not(a15), not(a2)], [a5, not(a12), not(a15)], [not(a6), a17, a5], [not(a13), a5, not(a19)], [a20, not(a1), a14], [a9, not(a17), a15], [not(a5), a19, not(a18)], [not(a12), a8, not(a10)], [not(a18), a14, not(a4)], [a15, not(a9), a13], [a9, not(a5), not(a1)], [a10, not(a19), not(a14)], [a20, a9, a4], [not(a9), not(a2), a19], [not(a5), a13, not(a17)], [a2, not(a10), not(a18)], [not(a18), a3, a11], [a7, not(a9), a17], [not(a15), not(a6), not(a3)], [not(a2), a3, not(a13)], [a12, a3, not(a2)], [not(a2), not(a3), a17], [a20, not(a15), not(a16)], [not(a5), not(a17), not(a19)], [not(a20), not(a18), a11], [not(a9), a1, not(a5)], [not(a19), a9, a17], [a12, not(a2), a17], [a4, not(a16), not(a5)]]).

unsat_dp1 :- dp([[a18, not(a8), a29], [not(a16), a3, a18], [not(a36), not(a11), not(a30)], [not(a50), a20, a32], [not(a6), a9, a35], [a42, not(a38), a29], [a43, not(a15), a10], [not(a48), not(a47), a1], [not(a45), not(a16), a33], [a38, a42, a22], [not(a49), a41, not(a34)], [a12, a17, a35], [a22, not(a49), a7], [not(a10), not(a11), not(a39)], [not(a28), not(a36), not(a37)], [not(a13), not(a46), not(a41)], [a21, not(a4), a9], [a12, a48, a10], [a24, a23, a15], [not(a8), not(a41), not(a43)], [not(a44), not(a2), not(a35)], [not(a27), a18, a31], [a47, a35, a6], [not(a11), not(a27), a41], [not(a33), not(a47), not(a45)], [not(a16), a36, not(a37)], [a27, not(a46), a2], [a15, not(a28), a10], [not(a38), a46, not(a39)], [not(a33), not(a4), a24], [not(a12), not(a45), a50], [not(a32), not(a21), not(a15)], [a8, a42, a24], [a30, not(a49), a4], [a45, not(a9), a28], [not(a33), not(a47), not(a1)], [a1, a27, not(a16)], [not(a11), not(a17), not(a35)], [not(a42), not(a15), a45], [not(a19), not(a27), a30], [a3, a28, a12], [a48, not(a11), not(a33)], [not(a6), a37, not(a9)], [not(a37), a13, not(a7)], [not(a2), a26, a16], [a46, not(a24), not(a38)], [not(a13), not(a24), not(a8)], [not(a36), not(a42), not(a21)], [not(a37), not(a19), a3], [not(a31), not(a50), a35], [not(a7), not(a26), a29], [not(a42), not(a45), a29], [a33, a25, not(a6)], [not(a45), not(a5), a7], [not(a7), a28, not(a6)], [not(a48), a31, not(a11)], [a32, a16, not(a37)], [not(a24), a48, a1], [a18, not(a46), a23], [not(a30), not(a50), a48], [not(a21), a39, not(a2)], [a24, a47, a42], [not(a36), a30, a4], [not(a5), a28, not(a1)], [not(a47), a32, not(a42)], [a16, a37, not(a22)], [not(a43), a42, not(a34)], [not(a40), a39, not(a20)], [not(a49), a29, a6], [not(a41), not(a3), a39], [not(a16), not(a12), a43], [a24, a22, a3], [a47, not(a45), a43], [a45, not(a37), a46], [not(a9), a26, a5], [not(a3), a23, not(a13)], [a5, not(a34), a13], [a12, a39, a13], [a22, a50, a37], [a19, a9, a46], [not(a24), a8, not(a27)], [not(a28), a7, a21], [a8, not(a25), a50], [a20, a50, a4], [a27, a36, a13], [a26, a31, not(a25)], [a39, not(a44), not(a32)], [not(a20), a41, not(a10)], [a49, not(a28), a35], [a1, a44, a34], [a39, a35, not(a11)], [not(a50), not(a42), not(a7)], [not(a24), a7, a47], [not(a13), a5, not(a48)], [not(a9), not(a20), not(a23)], [a2, a17, not(a19)], [a11, a23, a21], [not(a45), a30, a15], [a11, a26, not(a24)], [a38, a33, not(a13)], [a44, not(a27), not(a7)], [a41, a49, a2], [not(a18), a12, not(a37)], [not(a2), a12, not(a26)], [not(a19), a7, a32], [not(a22), a11, a33], [a8, a12, not(a20)], [a16, a40, not(a48)], [not(a2), not(a24), not(a11)], [a26, not(a17), a37], [not(a14), not(a19), a46], [a5, a47, a36], [not(a29), not(a9), a19], [a32, a4, a28], [not(a34), a20, not(a46)], [not(a4), not(a36), not(a13)], [not(a15), not(a37), a45], [not(a21), a29, a23], [not(a6), not(a40), a7], [not(a42), a31, not(a29)], [not(a36), a24, a31], [not(a45), not(a37), not(a1)], [a3, not(a6), not(a29)], [not(a28), not(a50), a27], [a44, a26, a5], [not(a17), not(a48), a49], [a12, not(a40), not(a7)], [not(a12), a31, not(a48)], [a27, a32, not(a42)], [not(a27), not(a10), a1], [a6, not(a49), a10], [not(a24), a8, a43], [a23, a31, a1], [a11, not(a47), a38], [not(a28), a26, not(a13)], [not(a40), a12, not(a42)], [not(a3), a39, a46], [a17, a41, a46], [a23, a21, a13], [not(a14), not(a1), not(a38)], [a20, a18, a6], [not(a50), a20, not(a9)], [a10, not(a32), not(a18)], [not(a21), a49, not(a34)], [a44, a23, not(a35)], [a40, not(a19), a34], [not(a1), a6, not(a12)], [a6, not(a2), not(a7)], [a32, not(a20), a34], [not(a12), a43, not(a29)], [a24, a2, not(a49)], [a10, not(a4), a40], [a11, a5, a12], [not(a3), a47, not(a31)], [a43, not(a23), a21], [not(a41), not(a36), not(a50)], [not(a8), not(a42), not(a24)], [a39, a45, a7], [a7, a37, not(a45)], [a41, a40, a8], [not(a50), not(a10), not(a8)], [not(a5), not(a39), not(a14)], [not(a22), not(a24), not(a43)], [not(a36), a40, a35], [a17, a49, a41], [not(a32), a7, a24], [not(a30), not(a8), not(a9)], [not(a41), not(a13), not(a10)], [a31, a26, not(a33)], [a17, not(a22), not(a39)], [not(a21), a28, a3], [not(a14), a46, a23], [a29, a16, a19], [a42, not(a32), not(a44)], [not(a24), a10, a23], [not(a1), not(a32), not(a21)], [not(a8), not(a44), not(a39)], [a39, a11, a9], [a19, a14, not(a46)], [a46, a44, not(a42)], [a37, a23, not(a29)], [a32, a25, a20], [a14, not(a43), not(a12)], [not(a36), not(a18), a46], [a14, not(a26), not(a10)], [not(a2), not(a30), a5], [a6, not(a18), a46], [not(a26), a2, not(a44)], [a20, not(a8), not(a11)], [not(a31), a3, a16], [not(a22), not(a9), a39], [not(a49), a44, not(a42)], [not(a45), not(a44), a31], [not(a31), a50, not(a11)], [not(a32), not(a46), a2], [not(a6), not(a7), a17], [a19, not(a32), a48], [a39, a20, not(a10)], [not(a22), not(a37), a38], [not(a31), a9, not(a48)], [a40, a12, a7], [not(a24), not(a4), a9], [not(a22), a49, a33], [not(a12), a43, a10], [a25, not(a30), not(a10)], [a46, a47, a31], [a13, a27, not(a7)], [not(a45), a32, not(a35)], [not(a50), a34, a9], [a2, a34, a30], [a3, a16, a2], [not(a18), a45, not(a12)], [a33, a37, a10], [a43, a7, not(a18)], [not(a22), a44, not(a19)], [not(a31), not(a27), not(a42)], [not(a3), not(a40), a8], [not(a23), not(a31), a38]]).
unsat_dll1 :- dll([[a18, not(a8), a29], [not(a16), a3, a18], [not(a36), not(a11), not(a30)], [not(a50), a20, a32], [not(a6), a9, a35], [a42, not(a38), a29], [a43, not(a15), a10], [not(a48), not(a47), a1], [not(a45), not(a16), a33], [a38, a42, a22], [not(a49), a41, not(a34)], [a12, a17, a35], [a22, not(a49), a7], [not(a10), not(a11), not(a39)], [not(a28), not(a36), not(a37)], [not(a13), not(a46), not(a41)], [a21, not(a4), a9], [a12, a48, a10], [a24, a23, a15], [not(a8), not(a41), not(a43)], [not(a44), not(a2), not(a35)], [not(a27), a18, a31], [a47, a35, a6], [not(a11), not(a27), a41], [not(a33), not(a47), not(a45)], [not(a16), a36, not(a37)], [a27, not(a46), a2], [a15, not(a28), a10], [not(a38), a46, not(a39)], [not(a33), not(a4), a24], [not(a12), not(a45), a50], [not(a32), not(a21), not(a15)], [a8, a42, a24], [a30, not(a49), a4], [a45, not(a9), a28], [not(a33), not(a47), not(a1)], [a1, a27, not(a16)], [not(a11), not(a17), not(a35)], [not(a42), not(a15), a45], [not(a19), not(a27), a30], [a3, a28, a12], [a48, not(a11), not(a33)], [not(a6), a37, not(a9)], [not(a37), a13, not(a7)], [not(a2), a26, a16], [a46, not(a24), not(a38)], [not(a13), not(a24), not(a8)], [not(a36), not(a42), not(a21)], [not(a37), not(a19), a3], [not(a31), not(a50), a35], [not(a7), not(a26), a29], [not(a42), not(a45), a29], [a33, a25, not(a6)], [not(a45), not(a5), a7], [not(a7), a28, not(a6)], [not(a48), a31, not(a11)], [a32, a16, not(a37)], [not(a24), a48, a1], [a18, not(a46), a23], [not(a30), not(a50), a48], [not(a21), a39, not(a2)], [a24, a47, a42], [not(a36), a30, a4], [not(a5), a28, not(a1)], [not(a47), a32, not(a42)], [a16, a37, not(a22)], [not(a43), a42, not(a34)], [not(a40), a39, not(a20)], [not(a49), a29, a6], [not(a41), not(a3), a39], [not(a16), not(a12), a43], [a24, a22, a3], [a47, not(a45), a43], [a45, not(a37), a46], [not(a9), a26, a5], [not(a3), a23, not(a13)], [a5, not(a34), a13], [a12, a39, a13], [a22, a50, a37], [a19, a9, a46], [not(a24), a8, not(a27)], [not(a28), a7, a21], [a8, not(a25), a50], [a20, a50, a4], [a27, a36, a13], [a26, a31, not(a25)], [a39, not(a44), not(a32)], [not(a20), a41, not(a10)], [a49, not(a28), a35], [a1, a44, a34], [a39, a35, not(a11)], [not(a50), not(a42), not(a7)], [not(a24), a7, a47], [not(a13), a5, not(a48)], [not(a9), not(a20), not(a23)], [a2, a17, not(a19)], [a11, a23, a21], [not(a45), a30, a15], [a11, a26, not(a24)], [a38, a33, not(a13)], [a44, not(a27), not(a7)], [a41, a49, a2], [not(a18), a12, not(a37)], [not(a2), a12, not(a26)], [not(a19), a7, a32], [not(a22), a11, a33], [a8, a12, not(a20)], [a16, a40, not(a48)], [not(a2), not(a24), not(a11)], [a26, not(a17), a37], [not(a14), not(a19), a46], [a5, a47, a36], [not(a29), not(a9), a19], [a32, a4, a28], [not(a34), a20, not(a46)], [not(a4), not(a36), not(a13)], [not(a15), not(a37), a45], [not(a21), a29, a23], [not(a6), not(a40), a7], [not(a42), a31, not(a29)], [not(a36), a24, a31], [not(a45), not(a37), not(a1)], [a3, not(a6), not(a29)], [not(a28), not(a50), a27], [a44, a26, a5], [not(a17), not(a48), a49], [a12, not(a40), not(a7)], [not(a12), a31, not(a48)], [a27, a32, not(a42)], [not(a27), not(a10), a1], [a6, not(a49), a10], [not(a24), a8, a43], [a23, a31, a1], [a11, not(a47), a38], [not(a28), a26, not(a13)], [not(a40), a12, not(a42)], [not(a3), a39, a46], [a17, a41, a46], [a23, a21, a13], [not(a14), not(a1), not(a38)], [a20, a18, a6], [not(a50), a20, not(a9)], [a10, not(a32), not(a18)], [not(a21), a49, not(a34)], [a44, a23, not(a35)], [a40, not(a19), a34], [not(a1), a6, not(a12)], [a6, not(a2), not(a7)], [a32, not(a20), a34], [not(a12), a43, not(a29)], [a24, a2, not(a49)], [a10, not(a4), a40], [a11, a5, a12], [not(a3), a47, not(a31)], [a43, not(a23), a21], [not(a41), not(a36), not(a50)], [not(a8), not(a42), not(a24)], [a39, a45, a7], [a7, a37, not(a45)], [a41, a40, a8], [not(a50), not(a10), not(a8)], [not(a5), not(a39), not(a14)], [not(a22), not(a24), not(a43)], [not(a36), a40, a35], [a17, a49, a41], [not(a32), a7, a24], [not(a30), not(a8), not(a9)], [not(a41), not(a13), not(a10)], [a31, a26, not(a33)], [a17, not(a22), not(a39)], [not(a21), a28, a3], [not(a14), a46, a23], [a29, a16, a19], [a42, not(a32), not(a44)], [not(a24), a10, a23], [not(a1), not(a32), not(a21)], [not(a8), not(a44), not(a39)], [a39, a11, a9], [a19, a14, not(a46)], [a46, a44, not(a42)], [a37, a23, not(a29)], [a32, a25, a20], [a14, not(a43), not(a12)], [not(a36), not(a18), a46], [a14, not(a26), not(a10)], [not(a2), not(a30), a5], [a6, not(a18), a46], [not(a26), a2, not(a44)], [a20, not(a8), not(a11)], [not(a31), a3, a16], [not(a22), not(a9), a39], [not(a49), a44, not(a42)], [not(a45), not(a44), a31], [not(a31), a50, not(a11)], [not(a32), not(a46), a2], [not(a6), not(a7), a17], [a19, not(a32), a48], [a39, a20, not(a10)], [not(a22), not(a37), a38], [not(a31), a9, not(a48)], [a40, a12, a7], [not(a24), not(a4), a9], [not(a22), a49, a33], [not(a12), a43, a10], [a25, not(a30), not(a10)], [a46, a47, a31], [a13, a27, not(a7)], [not(a45), a32, not(a35)], [not(a50), a34, a9], [a2, a34, a30], [a3, a16, a2], [not(a18), a45, not(a12)], [a33, a37, a10], [a43, a7, not(a18)], [not(a22), a44, not(a19)], [not(a31), not(a27), not(a42)], [not(a3), not(a40), a8], [not(a23), not(a31), a38]]).

unsat_dp2 :- dp([[b100], [not(b100)], [a10, a9, not(a6)], [a8, a19, a10], [a1, a18, a13], [not(a20), a18, a8], [a12, a18, a15], [a19, not(a14), not(a5)], [not(a3), not(a2), not(a17)], [a10, not(a9), a18], [not(a4), not(a17), a3], [not(a20), not(a5), not(a3)], [a17, not(a13), not(a4)], [a14, not(a1), a19], [a7, a3, not(a18)], [not(a9), not(a8), a12], [not(a17), not(a19), a10], [not(a10), not(a11), not(a17)], [a10, not(a5), a15], [not(a17), a2, not(a10)], [not(a9), a14, not(a1)], [not(a4), not(a1), not(a19)], [not(a17), a9, not(a3)], [a8, not(a11), not(a19)], [not(a9), a14, not(a15)], [not(a11), not(a16), not(a12)], [a11, not(a19), not(a17)], [a2, a9, a5], [not(a18), not(a9), not(a17)], [a9, not(a19), not(a8)], [not(a2), not(a6), a10], [a10, not(a8), not(a2)], [a2, a19, not(a6)], [not(a20), a12, a8], [a4, not(a1), a9], [a9, not(a2), not(a14)], [not(a11), a7, not(a20)], [a17, a3, not(a14)], [a15, not(a5), not(a9)], [not(a4), a12, not(a13)], [a19, a9, a10], [a11, not(a13), not(a6)], [a4, a20, a12], [a20, a9, a18], [not(a6), a12, a20], [a14, a1, a15], [not(a9), not(a12), not(a15)], [a12, a1, not(a11)], [a12, a6, not(a3)], [not(a18), a13, a3], [a4, a6, not(a19)], [not(a14), a18, not(a8)], [a16, a15, not(a2)], [not(a8), a12, not(a2)], [not(a8), a5, not(a16)], [a1, a15, not(a18)], [a20, not(a19), not(a11)], [not(a6), not(a10), a8], [not(a18), not(a11), a2], [not(a1), a18, not(a17)], [a19, a2, a13], [not(a5), not(a2), not(a20)], [not(a18), a5, a6], [a13, a15, a8], [a6, not(a5), not(a4)], [a3, not(a14), a12], [a11, not(a18), not(a1)], [a1, not(a19), a20], [not(a11), not(a7), a18], [a6, a18, a9], [not(a9), not(a4), a14], [a1, a7, not(a2)], [a4, not(a19), not(a17)], [not(a20), not(a19), a18], [not(a2), a8, not(a11)], [not(a19), a13, not(a4)], [a20, a4, a1], [not(a18), not(a11), not(a20)], [not(a15), not(a19), not(a10)], [a14, a17, not(a8)], [not(a15), a7, not(a9)], [not(a12), a5, a15], [not(a12), not(a3), not(a13)], [not(a2), a12, a11], [not(a11), not(a16), a3], [not(a14), a17, not(a3)], [not(a4), not(a6), a8], [not(a7), not(a14), not(a2)], [not(a19), a2, a4], [not(a1), not(a20), a11], [not(a12), a13, not(a18)], [a8, not(a4), a16], [not(a9), a6, a19]]).
unsat_dll2 :- dll([[a10, a9, not(a6)], [a8, a19, a10], [a1, a18, a13], [not(a20), a18, a8], [a12, a18, a15], [a19, not(a14), not(a5)], [not(a3), not(a2), not(a17)], [a10, not(a9), a18], [not(a4), not(a17), a3], [not(a20), not(a5), not(a3)], [a17, not(a13), not(a4)], [a14, not(a1), a19], [a7, a3, not(a18)], [not(a9), not(a8), a12], [not(a17), not(a19), a10], [not(a10), not(a11), not(a17)], [a10, not(a5), a15], [not(a17), a2, not(a10)], [not(a9), a14, not(a1)], [not(a4), not(a1), not(a19)], [not(a17), a9, not(a3)], [a8, not(a11), not(a19)], [not(a9), a14, not(a15)], [not(a11), not(a16), not(a12)], [a11, not(a19), not(a17)], [a2, a9, a5], [not(a18), not(a9), not(a17)], [a9, not(a19), not(a8)], [not(a2), not(a6), a10], [a10, not(a8), not(a2)], [a2, a19, not(a6)], [not(a20), a12, a8], [a4, not(a1), a9], [a9, not(a2), not(a14)], [not(a11), a7, not(a20)], [a17, a3, not(a14)], [a15, not(a5), not(a9)], [not(a4), a12, not(a13)], [a19, a9, a10], [a11, not(a13), not(a6)], [a4, a20, a12], [a20, a9, a18], [not(a6), a12, a20], [a14, a1, a15], [not(a9), not(a12), not(a15)], [a12, a1, not(a11)], [a12, a6, not(a3)], [not(a18), a13, a3], [a4, a6, not(a19)], [not(a14), a18, not(a8)], [a16, a15, not(a2)], [not(a8), a12, not(a2)], [not(a8), a5, not(a16)], [a1, a15, not(a18)], [a20, not(a19), not(a11)], [not(a6), not(a10), a8], [not(a18), not(a11), a2], [not(a1), a18, not(a17)], [a19, a2, a13], [not(a5), not(a2), not(a20)], [not(a18), a5, a6], [a13, a15, a8], [a6, not(a5), not(a4)], [a3, not(a14), a12], [a11, not(a18), not(a1)], [a1, not(a19), a20], [not(a11), not(a7), a18], [a6, a18, a9], [not(a9), not(a4), a14], [a1, a7, not(a2)], [a4, not(a19), not(a17)], [not(a20), not(a19), a18], [not(a2), a8, not(a11)], [not(a19), a13, not(a4)], [a20, a4, a1], [not(a18), not(a11), not(a20)], [not(a15), not(a19), not(a10)], [a14, a17, not(a8)], [not(a15), a7, not(a9)], [not(a12), a5, a15], [not(a12), not(a3), not(a13)], [not(a2), a12, a11], [not(a11), not(a16), a3], [not(a14), a17, not(a3)], [not(a4), not(a6), a8], [not(a7), not(a14), not(a2)], [not(a19), a2, a4], [not(a1), not(a20), a11], [not(a12), a13, not(a18)], [a8, not(a4), a16], [not(a9), a6, a19], [b100], [not(b100)]]).

unsat_dp3 :-  dp([[a37, a43, not(a45)], [a32, a44, not(a49)], [not(a25), not(a43), not(a32)], [a47, not(a37), not(a5)], [not(a1), a31, a44], [not(a42), a44, a50], [not(a31), a33, not(a16)], [a28, not(a32), a18], [not(a39), not(a24), a46], [not(a33), not(a45), a5], [not(a34), a21, a6], [a6, a38, not(a39)], [a47, a44, a28], [a23, not(a42), a28], [not(a42), not(a17), a47], [a26, a17, a14], [not(a15), not(a12), a8], [a32, not(a22), a45], [not(a16), not(a14), not(a35)], [a17, not(a2), not(a23)], [not(a36), not(a14), a44], [not(a9), not(a49), a20], [a26, a48, not(a5)], [a38, not(a37), not(a4)], [a48, a3, not(a41)], [not(a50), not(a48), not(a2)], [a5, not(a1), a39], [a49, not(a20), not(a12)], [not(a43), not(a27), a20], [a35, a46, a8], [a13, a16, a17], [not(a4), not(a13), a9], [a7, not(a36), a23], [a1, not(a32), not(a40)], [not(a25), not(a12), not(a34)], [a2, a50, a15], [not(a27), a18, a36], [a39, not(a16), not(a9)], [a25, a34, a29], [not(a2), a29, a18], [not(a35), not(a13), a3], [a23, not(a8), not(a34)], [not(a32), not(a33), not(a8)], [a38, not(a19), not(a25)], [not(a22), a34, a6], [not(a43), a4, a29], [not(a12), not(a27), a18], [not(a37), a16, not(a44)], [a35, a44, not(a6)], [not(a37), a31, not(a22)], [not(a9), a12, not(a45)], [a48, a18, a25], [a27, not(a49), not(a24)], [a8, not(a28), not(a23)], [a2, a24, not(a13)], [a14, a25, not(a44)], [not(a6), a10, not(a18)], [a39, a1, a28], [a42, not(a29), not(a48)], [a47, a44, a8], [not(a42), not(a30), a48], [a36, a43, not(a20)], [a32, a11, a44], [not(a30), not(a14), not(a43)], [a13, not(a26), not(a28)], [not(a43), a27, a23], [a1, a48, a2], [a13, not(a33), a34], [a22, not(a23), not(a20)], [not(a49), not(a13), a24], [not(a20), a25, not(a36)], [a2, not(a16), not(a45)], [a27, a48, a28], [not(a17), not(a26), not(a42)], [a34, a38, not(a4)], [a16, a33, not(a11)], [not(a49), not(a27), not(a41)], [a39, a6, not(a23)], [not(a37), a33, not(a2)], [a20, a3, not(a28)], [a9, not(a25), not(a23)], [a45, a24, a35], [a6, a9, a33], [not(a8), a10, a36], [a28, not(a30), a37], [not(a41), a8, a38], [a12, not(a37), not(a29)], [not(a23), not(a28), a6], [not(a5), not(a46), a50], [not(a8), not(a24), a35], [not(a7), a32, not(a30)], [not(a6), not(a31), a18], [a18, not(a42), not(a23)], [a20, a24, not(a37)], [a9, not(a43), not(a26)], [a10, not(a16), a29], [not(a9), a16, not(a27)], [not(a10), not(a28), a32], [a20, a12, a32], [a47, a20, not(a44)], [not(a21), not(a32), not(a43)], [not(a8), not(a45), a44], [a25, not(a47), a31], [not(a14), a48, not(a35)], [not(a47), a50, not(a16)], [a17, not(a43), a21], [not(a37), not(a49), not(a50)], [a34, a9, a33], [a38, a28, a9], [not(a18), a20, not(a12)], [not(a23), a26, not(a43)], [a22, not(a16), not(a49)], [a36, a8, not(a18)], [a38, not(a49), not(a10)], [a42, not(a12), not(a11)], [not(a26), a21, not(a11)], [a3, a23, a35], [not(a9), a25, a21], [not(a28), not(a41), not(a17)], [not(a42), not(a2), not(a5)], [not(a17), a16, not(a14)], [not(a9), a5, a11], [not(a14), not(a15), not(a42)], [a41, a22, not(a36)], [a2, a13, a28], [a45, not(a21), not(a39)], [a46, not(a7), a47], [a23, not(a13), a17], [not(a11), not(a37), a33], [not(a22), a46, a16], [a23, a47, not(a40)], [not(a3), a1, not(a43)], [a1, not(a29), not(a5)], [a29, not(a4), not(a36)], [not(a14), a22, not(a26)], [not(a50), a43, not(a24)], [a26, a7, not(a29)], [a12, a6, a13], [a16, a2, a10], [a31, a26, a30], [a33, not(a5), not(a44)], [a35, not(a20), a4], [a47, a50, not(a14)], [a15, not(a30), not(a38)], [a33, a12, not(a25)], [a13, a50, not(a35)], [a4, a41, not(a48)], [not(a15), a1, a36], [a15, not(a24), a31], [not(a2), not(a31), not(a23)], [not(a7), a6, not(a40)], [a19, a15, not(a37)], [not(a3), a36, not(a41)], [a38, not(a28), a24], [a30, a32, not(a2)], [not(a42), a14, a50], [a27, not(a23), not(a26)], [not(a3), not(a42), not(a33)], [a43, not(a17), a24], [not(a37), a15, not(a35)], [not(a33), not(a9), a6], [a43, not(a16), a33], [not(a16), a31, not(a14)], [a45, not(a16), not(a9)], [a22, a18, a9], [a48, a39, a33], [not(a13), a38, a45], [not(a48), a46, a30], [a41, a36, a31], [not(a30), not(a35), a34], [not(a32), not(a29), a42], [not(a47), not(a11), a1], [not(a9), not(a40), not(a12)], [not(a10), not(a27), not(a17)], [not(a16), not(a15), a17], [not(a8), a32, not(a36)], [a12, a13, not(a46)], [not(a28), a12, a39], [a10, a40, a36], [a17, not(a39), not(a35)], [a23, not(a20), a28], [not(a33), a47, not(a8)], [a22, not(a13), not(a10)], [a22, not(a25), not(a15)], [a39, not(a38), a18], [not(a27), not(a45), not(a38)], [a30, not(a26), a7], [a45, a39, a23], [not(a34), not(a23), not(a32)], [not(a30), not(a33), not(a19)], [not(a6), a13, a38], [not(a42), a39, a43], [a49, a8, not(a22)], [not(a46), a31, not(a11)], [a23, not(a7), a10], [a26, a5, a41], [a11, a3, a49], [not(a7), not(a23), not(a25)], [a7, a30, not(a13)], [a9, a45, not(a44)], [a21, a39, a42], [not(a18), a9, not(a17)], [a33, not(a47), not(a10)], [not(a18), not(a10), not(a5)], [a44, not(a27), a36], [not(a33), not(a29), a15], [not(a11), not(a4), a29], [a11, a12, not(a50)], [a12, a40, a17], [not(a18), not(a48), a45], [a11, a17, a32], [not(a15), not(a6), not(a31)], [a2, a47, a33], [a34, not(a8), a3], [a9, not(a49), a22], [a20, not(a39), not(a27)], [not(a3), not(a7), a35], [not(a16), a50, not(a15)]]).
unsat_dll3 :- dll([[a37, a43, not(a45)], [a32, a44, not(a49)], [not(a25), not(a43), not(a32)], [a47, not(a37), not(a5)], [not(a1), a31, a44], [not(a42), a44, a50], [not(a31), a33, not(a16)], [a28, not(a32), a18], [not(a39), not(a24), a46], [not(a33), not(a45), a5], [not(a34), a21, a6], [a6, a38, not(a39)], [a47, a44, a28], [a23, not(a42), a28], [not(a42), not(a17), a47], [a26, a17, a14], [not(a15), not(a12), a8], [a32, not(a22), a45], [not(a16), not(a14), not(a35)], [a17, not(a2), not(a23)], [not(a36), not(a14), a44], [not(a9), not(a49), a20], [a26, a48, not(a5)], [a38, not(a37), not(a4)], [a48, a3, not(a41)], [not(a50), not(a48), not(a2)], [a5, not(a1), a39], [a49, not(a20), not(a12)], [not(a43), not(a27), a20], [a35, a46, a8], [a13, a16, a17], [not(a4), not(a13), a9], [a7, not(a36), a23], [a1, not(a32), not(a40)], [not(a25), not(a12), not(a34)], [a2, a50, a15], [not(a27), a18, a36], [a39, not(a16), not(a9)], [a25, a34, a29], [not(a2), a29, a18], [not(a35), not(a13), a3], [a23, not(a8), not(a34)], [not(a32), not(a33), not(a8)], [a38, not(a19), not(a25)], [not(a22), a34, a6], [not(a43), a4, a29], [not(a12), not(a27), a18], [not(a37), a16, not(a44)], [a35, a44, not(a6)], [not(a37), a31, not(a22)], [not(a9), a12, not(a45)], [a48, a18, a25], [a27, not(a49), not(a24)], [a8, not(a28), not(a23)], [a2, a24, not(a13)], [a14, a25, not(a44)], [not(a6), a10, not(a18)], [a39, a1, a28], [a42, not(a29), not(a48)], [a47, a44, a8], [not(a42), not(a30), a48], [a36, a43, not(a20)], [a32, a11, a44], [not(a30), not(a14), not(a43)], [a13, not(a26), not(a28)], [not(a43), a27, a23], [a1, a48, a2], [a13, not(a33), a34], [a22, not(a23), not(a20)], [not(a49), not(a13), a24], [not(a20), a25, not(a36)], [a2, not(a16), not(a45)], [a27, a48, a28], [not(a17), not(a26), not(a42)], [a34, a38, not(a4)], [a16, a33, not(a11)], [not(a49), not(a27), not(a41)], [a39, a6, not(a23)], [not(a37), a33, not(a2)], [a20, a3, not(a28)], [a9, not(a25), not(a23)], [a45, a24, a35], [a6, a9, a33], [not(a8), a10, a36], [a28, not(a30), a37], [not(a41), a8, a38], [a12, not(a37), not(a29)], [not(a23), not(a28), a6], [not(a5), not(a46), a50], [not(a8), not(a24), a35], [not(a7), a32, not(a30)], [not(a6), not(a31), a18], [a18, not(a42), not(a23)], [a20, a24, not(a37)], [a9, not(a43), not(a26)], [a10, not(a16), a29], [not(a9), a16, not(a27)], [not(a10), not(a28), a32], [a20, a12, a32], [a47, a20, not(a44)], [not(a21), not(a32), not(a43)], [not(a8), not(a45), a44], [a25, not(a47), a31], [not(a14), a48, not(a35)], [not(a47), a50, not(a16)], [a17, not(a43), a21], [not(a37), not(a49), not(a50)], [a34, a9, a33], [a38, a28, a9], [not(a18), a20, not(a12)], [not(a23), a26, not(a43)], [a22, not(a16), not(a49)], [a36, a8, not(a18)], [a38, not(a49), not(a10)], [a42, not(a12), not(a11)], [not(a26), a21, not(a11)], [a3, a23, a35], [not(a9), a25, a21], [not(a28), not(a41), not(a17)], [not(a42), not(a2), not(a5)], [not(a17), a16, not(a14)], [not(a9), a5, a11], [not(a14), not(a15), not(a42)], [a41, a22, not(a36)], [a2, a13, a28], [a45, not(a21), not(a39)], [a46, not(a7), a47], [a23, not(a13), a17], [not(a11), not(a37), a33], [not(a22), a46, a16], [a23, a47, not(a40)], [not(a3), a1, not(a43)], [a1, not(a29), not(a5)], [a29, not(a4), not(a36)], [not(a14), a22, not(a26)], [not(a50), a43, not(a24)], [a26, a7, not(a29)], [a12, a6, a13], [a16, a2, a10], [a31, a26, a30], [a33, not(a5), not(a44)], [a35, not(a20), a4], [a47, a50, not(a14)], [a15, not(a30), not(a38)], [a33, a12, not(a25)], [a13, a50, not(a35)], [a4, a41, not(a48)], [not(a15), a1, a36], [a15, not(a24), a31], [not(a2), not(a31), not(a23)], [not(a7), a6, not(a40)], [a19, a15, not(a37)], [not(a3), a36, not(a41)], [a38, not(a28), a24], [a30, a32, not(a2)], [not(a42), a14, a50], [a27, not(a23), not(a26)], [not(a3), not(a42), not(a33)], [a43, not(a17), a24], [not(a37), a15, not(a35)], [not(a33), not(a9), a6], [a43, not(a16), a33], [not(a16), a31, not(a14)], [a45, not(a16), not(a9)], [a22, a18, a9], [a48, a39, a33], [not(a13), a38, a45], [not(a48), a46, a30], [a41, a36, a31], [not(a30), not(a35), a34], [not(a32), not(a29), a42], [not(a47), not(a11), a1], [not(a9), not(a40), not(a12)], [not(a10), not(a27), not(a17)], [not(a16), not(a15), a17], [not(a8), a32, not(a36)], [a12, a13, not(a46)], [not(a28), a12, a39], [a10, a40, a36], [a17, not(a39), not(a35)], [a23, not(a20), a28], [not(a33), a47, not(a8)], [a22, not(a13), not(a10)], [a22, not(a25), not(a15)], [a39, not(a38), a18], [not(a27), not(a45), not(a38)], [a30, not(a26), a7], [a45, a39, a23], [not(a34), not(a23), not(a32)], [not(a30), not(a33), not(a19)], [not(a6), a13, a38], [not(a42), a39, a43], [a49, a8, not(a22)], [not(a46), a31, not(a11)], [a23, not(a7), a10], [a26, a5, a41], [a11, a3, a49], [not(a7), not(a23), not(a25)], [a7, a30, not(a13)], [a9, a45, not(a44)], [a21, a39, a42], [not(a18), a9, not(a17)], [a33, not(a47), not(a10)], [not(a18), not(a10), not(a5)], [a44, not(a27), a36], [not(a33), not(a29), a15], [not(a11), not(a4), a29], [a11, a12, not(a50)], [a12, a40, a17], [not(a18), not(a48), a45], [a11, a17, a32], [not(a15), not(a6), not(a31)], [a2, a47, a33], [a34, not(a8), a3], [a9, not(a49), a22], [a20, not(a39), not(a27)], [not(a3), not(a7), a35], [not(a16), a50, not(a15)]]).

tests_dp :- sat_dp1, sat_dp2, \+ unsat_dp1, \+ unsat_dp2, \+ unsat_dp3.
tests_dll :- sat_dll1, sat_dll2, \+ unsat_dll1, \+ unsat_dll2, \+ unsat_dll3.
