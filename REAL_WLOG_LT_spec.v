Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1866512 : forall (P : real -> real -> Prop), ((forall x : real, P x x) /\ ((forall x : real, forall y : real, (P x y) = (P y x)) /\ (forall x : real, forall y : real, (real_lt x y) -> P x y))) -> forall x : real, forall y : real, P x y.
