Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5285051 : forall s : real -> Prop, forall c : real, ((~ (s = (@EMPTY real))) /\ ((exists b : real, forall x : real, (@IN real x s) -> real_le b x) /\ (real_lt (inf s) c))) -> exists x : real, (@IN real x s) /\ (real_lt x c).
