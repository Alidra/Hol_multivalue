Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem17934 : forall {A : Type'} (x : A) (y : A), (fun y' : A => (x = y') = (y' = x)) y.
