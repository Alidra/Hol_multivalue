Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18392 : forall {A : Type'} (P : A -> Prop), (~ (all P)) = (exists x : A, ~ (P x)).
