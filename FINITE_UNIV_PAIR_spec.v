Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4334179 : forall {A : Type'}, (@FINITE (prod A A) (@UNIV (prod A A))) = (@FINITE A (@UNIV A)).
