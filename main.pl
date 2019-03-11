:- use_module(library(lists)).
:- use_module(library(ordset)).

% Definitions of true and false
top.
bot :- fail.

% The negate procedure
negate(not(A), A) :- !.
negate(A, not(A)).

% Removes Duplicates
remove_duplicates(List, ListWithoutDuplicates) :- sort(List, ListWithoutDuplicates).


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



% PROCEDURE TO GET ALL LITERALS 

% Gets a list of all the literals in the clauses
all_literals(Clauses, Literals) :- 
    positive_and_negative_literals(Clauses, PosAndNegLits),
    unsigned_literals(PosAndNegLits, UnsignedLiterals), % Removes negations like - not a
    remove_duplicates(UnsignedLiterals, Literals).
		
% unsigned_literals(PosAndNegLits, Literals) keeps only the unsigned version of the literal
% so the literal x1 or the literal not x1 will both be converted to x1.
unsigned_literals([], []).
unsigned_literals([not(A)|T], [A|Literals]) :- !, unsigned_literals(T, Literals).
unsigned_literals([A|T], [A|Literals]) :- !, unsigned_literals(T, Literals).

% Simply gets all the literals from the clauses be it be a positive or negated literal.
positive_and_negative_literals(Clauses, PosAndNegLits) :-
    flatten(Clauses, RepeatedLiterals), 
    remove_duplicates(RepeatedLiterals, PosAndNegLits). % Removes Duplicates



% CLAUSE REFINEMENTS

% Superset Elimination
is_superset(X, Y) :- ord_subset(Y, X).

is_superset_of_a_elem(_, []) :- fail.
is_superset_of_a_elem(X, [H|_]) :- 
    is_superset(X, H), !.
is_superset_of_a_elem(X, [H|T]) :- 
    \+ is_superset(X, H), is_superset_of_a_elem(X, T).

eliminate_superset_clauses_in_one_direction([L], [L]).
eliminate_superset_clauses_in_one_direction([Clause|Clauses], FilteredClauses) :-
	is_superset_of_a_elem(Clause, Clauses), !,
	eliminate_superset_clauses_in_one_direction(Clauses, FilteredClauses).
eliminate_superset_clauses_in_one_direction([Clause|Clauses], [Clause|FilteredClauses]) :-
	\+ is_superset_of_a_elem(Clause, Clauses),
	eliminate_superset_clauses_in_one_direction(Clauses, FilteredClauses).

eliminate_superset_clauses([], []) :- !.
eliminate_superset_clauses(Clauses, FilteredClauses) :-
    eliminate_superset_clauses_in_one_direction(Clauses, OnePassClauses),
    reverse(OnePassClauses, ReversedClauses),
    eliminate_superset_clauses_in_one_direction(ReversedClauses, FilteredClauses).


% Duplicate Literal Elimination
elimiate_duplicate_literals_in_clauses([], []).
elimiate_duplicate_literals_in_clauses([Clause|Clauses], NoDupClauses) :-
    remove_duplicates(Clause, ClauseWithoutDuplicates),
    elimiate_duplicate_literals_in_clauses(Clauses, OtherFilteredClauses),
    NoDupClauses = [ClauseWithoutDuplicates|OtherFilteredClauses].

% Duplicate Clause Elimination - works because Duplicate Literal Elimination sorts the clauses
eliminate_duplicate_clauses([], []) :- !.
eliminate_duplicate_clauses(Clauses, NoDupClauses) :-
    remove_duplicates(Clauses, NoDupClauses).


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


% Pure Literal Elimination
%% Simple Helper Procedures for Pure Literal Elimination
remove_clauses_containing_literal(_, [], []).
remove_clauses_containing_literal(Lit, [Clause|Clauses], FilteredClauses) :-
    member(Lit, Clause), !, remove_clauses_containing_literal(Lit, Clauses, FilteredClauses).
remove_clauses_containing_literal(Lit, [Clause|Clauses], [Clause|FilteredClauses]) :-
    remove_clauses_containing_literal(Lit, Clauses, FilteredClauses).

remove_literal_from_clauses(_, [], []).
remove_literal_from_clauses(Lit, [Clause|Clauses], [FilteredClause|FilteredClauses]) :-
    remove(Lit, Clause, FilteredClause), remove_literal_from_clauses(Lit, Clauses, FilteredClauses).


% Gets a list of all the pure literals in the expression.
pure_literals([], []).
pure_literals(Clauses, PureLiterals) :-
    positive_and_negative_literals(Clauses, Literals),
    pure_literals_helper(Literals, PureLiterals).

pure_literals_helper([], []).
pure_literals_helper([Lit|Literals], [Lit|PureLiterals]) :-
    negate(Lit, NegLit), \+ member(NegLit, Literals), !,
    pure_literals_helper(Literals, PureLiterals).
pure_literals_helper([Lit|Literals], PureLiterals) :-
    negate(Lit, NegLit), 
    remove(Lit, Literals, FilteredLiteralsIntermediate),
    remove(NegLit, FilteredLiteralsIntermediate, FilteredLiterals),
    pure_literals_helper(FilteredLiterals, PureLiterals).


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


% Unit Clause Elimination
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
    remove_duplicates(UnitClauseLiteralsWithDuplicates, UnitClauseLiterals).

eliminate_unit_clauses(Clauses, UpdatedClauses) :-
  unit_clause_literals(Clauses, UnitClauseLiterals),
  unit_propogate_for_literals(UnitClauseLiterals, Clauses, UpdatedClauses).


% Refines Clauses using all the refinements above
basic_refine_clauses([], []).
basic_refine_clauses(Clauses, ImprovedClauses) :-
    elimiate_duplicate_literals_in_clauses(Clauses, NoDupLitClauses),
    eliminate_duplicate_clauses(NoDupLitClauses, NoDupClauses),
    eliminate_trivial_clauses(NoDupClauses, NonTrivialClauses),
    eliminate_superset_clauses(NonTrivialClauses, SupersetEliminatedClauses),
    ImprovedClauses = SupersetEliminatedClauses.

advanced_refine_clauses(Clauses, ImprovedClauses) :- 
    eliminate_pure_literals(Clauses, ClausesWithoutPureLiterals),
    eliminate_unit_clauses(ClausesWithoutPureLiterals, ClausesWithoutUnitLiterals),
    basic_refine_clauses(ClausesWithoutUnitLiterals, ImprovedClauses).


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


% resolve_separated_clause(Lit, PosClauses, NegClauses, CombinedClauses)
% This procedure is the main resolution procedure which removes the positive
% literal Lit from a clause and its negation from another clause and joins them
% to make a new clause. It goes through all pairs of clauses which contain positive Lit and
% negated Lit.
resolve_separated_clauses(_, PosClauses, [], PosClauses).
resolve_separated_clauses(_, [], NegClauses, NegClauses).
resolve_separated_clauses(Lit, [PosClause|PosClauses], NegClauses, Result) :-
    remove(Lit, PosClause, FilteredPosClause),
    negate(Lit, NegLit), remove_from_all(NegLit, NegClauses, FilteredNegClauses),
    append_to_all(FilteredPosClause, FilteredNegClauses, CombinedClauses),
    resolve_separated_clauses(Lit, PosClauses, NegClauses, MoreCombinedClauses),
    basic_refine_clauses(CombinedClauses, RefinedCombinedClauses),
    append(RefinedCombinedClauses, MoreCombinedClauses, IntermediateResults),
    basic_refine_clauses(IntermediateResults, Result).

% MAIN DP DRIVER CODE

dp([[]]) :- fail, !.
dp(Clauses) :-
	all_literals(Clauses, Literals),
  dp_helper(Clauses, Literals, FinalClauses),
  \+ member([], FinalClauses), !.


dp_helper([], _, []) :- !.
dp_helper(Clauses, [], Clauses) :- !.
dp_helper(Clauses, [Lit|OtherLit], OtherResolvants) :-
    \+ member([], Clauses), % Prune early if empty clause is found
    basic_refine_clauses(Clauses, ImprovedClauses),
    separate_clauses(Lit, ImprovedClauses, PosClauses, NegClauses, NeitherClauses),
    resolve_separated_clauses(Lit, PosClauses, NegClauses, Resolvents),
    \+ member([], Resolvents), % Prune early if empty clause is found
    append(Resolvents, NeitherClauses, UpdatedClauses),
    dp_helper(UpdatedClauses, OtherLit, OtherResolvants).



% MAIN DLL DRIVER CODE

unit_propogate(Clauses, UpdatedClauses) :- 
  eliminate_unit_clauses(Clauses, UpdatedClauses).

dll(Clauses) :-
    \+ member([], Clauses),
    all_literals(Clauses, Literals),
    dll_helper(Literals, Clauses).

dll_helper(_, []). % Satisfiable if empty cube
dll_helper([Lit|Literals], Clauses) :-
    \+ member([], Clauses), % Clauses contain empty clause then return false
    negate(Lit, NegLit),
    unit_propogate(Clauses, UpdatedClauses),
    union([[Lit]], UpdatedClauses, ClausesWithPosLit),
    union([[NegLit]], UpdatedClauses, ClausesWithNegLit),
    append(Literals, [Lit], UpdatedLiterals), % Rotate literals (i.e by choice for the choose_literal function)
    execute_or(
        UpdatedClauses = [], 
        dll_helper(UpdatedLiterals, ClausesWithPosLit), 
        dll_helper(UpdatedLiterals, ClausesWithNegLit)
    ).

execute_or(A, _, _) :- A, !.
execute_or(_, B, _) :- B, !.
execute_or(_, _, C) :- C, !.
