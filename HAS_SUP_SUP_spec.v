Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5297166 : forall s : real -> Prop, forall l : real, (has_sup s l) = ((~ (s = (@EMPTY real))) /\ ((exists b : real, forall x : real, (@IN real x s) -> real_le x b) /\ ((sup s) = l))).
