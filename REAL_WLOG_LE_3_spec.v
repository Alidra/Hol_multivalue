Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1868204 : forall P : real -> real -> real -> Prop, ((forall x : real, forall y : real, forall z : real, (P x y z) -> (P y x z) /\ (P x z y)) /\ (forall x : real, forall y : real, forall z : real, ((real_le x y) /\ (real_le y z)) -> P x y z)) -> forall x : real, forall y : real, forall z : real, P x y z.
