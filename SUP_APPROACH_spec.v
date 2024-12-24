Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5200089 : forall s : real -> Prop, forall c : real, ((~ (s = (@EMPTY real))) /\ ((exists b : real, forall x : real, (@IN real x s) -> real_le x b) /\ (real_lt c (sup s)))) -> exists x : real, (@IN real x s) /\ (real_lt c x).
