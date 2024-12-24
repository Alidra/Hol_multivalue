Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5323606 : forall s : real -> Prop, forall t : real -> Prop, forall l : real, forall m : real, ((has_inf s l) /\ ((has_inf t m) /\ (forall y : real, (@IN real y t) -> exists x : real, (@IN real x s) /\ (real_le x y)))) -> real_le l m.
