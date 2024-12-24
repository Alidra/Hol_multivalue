Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5327820 : forall s : real -> Prop, forall t : real -> Prop, forall l : real, forall m : real, ((has_sup s l) /\ ((has_sup t m) /\ (forall y : real, (@IN real y t) -> exists x : real, (@IN real x s) /\ (real_le y x)))) -> real_le m l.
