Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4333670 : forall {A B : Type'}, (@FINITE (prod A B) (@UNIV (prod A B))) = ((@FINITE A (@UNIV A)) /\ (@FINITE B (@UNIV B))).
