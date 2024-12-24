Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem17935 : forall {A : Type'} (y : A) (x : A), ((fun y' : A => (x = y') = (y' = x)) y) = ((x = y) = (y = x)).
