Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2313447 : forall (P : int -> int -> Prop), ((forall x : int, P x x) /\ ((forall x : int, forall y : int, (P x y) = (P y x)) /\ (forall x : int, forall y : int, (int_lt x y) -> P x y))) -> forall x : int, forall y : int, P x y.
