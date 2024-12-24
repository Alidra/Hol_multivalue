Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7607927 : forall {A : Type'}, @FINITE (finite_image A) (@UNIV (finite_image A)).
