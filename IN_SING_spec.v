Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3205876 : forall {A : Type'}, forall x : A, forall y : A, (@IN A x (@INSERT A y (@EMPTY A))) = (x = y).
