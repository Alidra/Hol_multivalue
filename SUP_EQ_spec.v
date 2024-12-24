Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5135108 : forall s : real -> Prop, forall t : real -> Prop, (forall b : real, (forall x : real, (@IN real x s) -> real_le x b) = (forall x : real, (@IN real x t) -> real_le x b)) -> (sup s) = (sup t).
