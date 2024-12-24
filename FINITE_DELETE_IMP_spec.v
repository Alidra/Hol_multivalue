Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3609207 : forall {A : Type'}, forall s : A -> Prop, forall x : A, (@FINITE A s) -> @FINITE A (@DELETE A s x).
