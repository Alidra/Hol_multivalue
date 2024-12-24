Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7936860 : forall {A : Type'}, (@FINITE unit (@UNIV unit)) /\ ((@FINITE (tybit0 A) (@UNIV (tybit0 A))) /\ (@FINITE (tybit1 A) (@UNIV (tybit1 A)))).
