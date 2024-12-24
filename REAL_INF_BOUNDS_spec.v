Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5243750 : forall s : real -> Prop, forall a : real, forall b : real, ((~ (s = (@EMPTY real))) /\ (forall x : real, (@IN real x s) -> (real_le a x) /\ (real_le x b))) -> (real_le a (inf s)) /\ (real_le (inf s) b).
