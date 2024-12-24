Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4593398 : forall {A B : Type'}, ((@FINITE A (@UNIV A)) /\ (@FINITE B (@UNIV B))) -> @FINITE (A -> B) (@UNIV (A -> B)).
