Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5166478 : forall s : real -> Prop, forall a : real, forall b : real, ((~ (s = (@EMPTY real))) /\ (forall x : real, (@IN real x s) -> (real_le a x) /\ (real_le x b))) -> (real_le a (sup s)) /\ (real_le (sup s) b).
