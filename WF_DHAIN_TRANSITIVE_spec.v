Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem318095 : forall {A : Type'}, forall lt2 : A -> A -> Prop, (forall x : A, forall y : A, forall z : A, ((lt2 x y) /\ (lt2 y z)) -> lt2 x z) -> (@WF A lt2) = (~ (exists s : nat -> A, forall i : nat, forall j : nat, (Peano.lt i j) -> lt2 (s j) (s i))).
