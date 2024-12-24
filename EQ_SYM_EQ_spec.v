Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem362 : forall {A : Type'}, forall x : A, forall y : A, (x = y) = (y = x).
