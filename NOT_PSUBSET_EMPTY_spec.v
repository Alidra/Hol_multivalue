Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3228395 : forall {A : Type'}, forall s : A -> Prop, ~ (@PSUBSET A s (@EMPTY A)).
