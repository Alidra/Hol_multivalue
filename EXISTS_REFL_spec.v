Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4363 : forall {A : Type'}, forall a : A, exists x : A, x = a.
