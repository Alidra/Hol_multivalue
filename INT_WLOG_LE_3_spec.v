Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2315139 : forall P : int -> int -> int -> Prop, ((forall x : int, forall y : int, forall z : int, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : int, forall y : int, forall z : int, ((int_le x y) /\ (int_le y z)) -> P x y z)) -> forall x : int, forall y : int, forall z : int, P x y z.
