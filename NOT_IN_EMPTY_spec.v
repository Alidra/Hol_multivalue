Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3204775 : forall {A : Type'}, forall x : A, ~ (@IN A x (@EMPTY A)).
