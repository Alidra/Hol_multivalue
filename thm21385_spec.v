Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem21385 : forall {A : Type'} (x : A) (y : A) (z : A), (~ (x = y)) \/ ((~ (x = z)) \/ (y = z)).
