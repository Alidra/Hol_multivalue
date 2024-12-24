Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7640397 : forall {M N : Type'}, (@FINITE (finite_sum M N) (@UNIV (finite_sum M N))) = ((@FINITE (finite_sum M N) (@UNIV (finite_sum M N))) = True).
