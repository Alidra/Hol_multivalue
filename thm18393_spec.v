Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem18393 : forall {A : Type'} (P : A -> Prop), (~ (@ex1 A P)) = ((forall x : A, ~ (P x)) \/ (exists x : A, exists y : A, (P x) /\ ((P y) /\ (~ (y = x))))).