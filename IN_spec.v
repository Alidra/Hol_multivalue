Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3181151 : forall {A : Type'}, forall P : A -> Prop, forall x : A, (@IN A x P) = (P x).
