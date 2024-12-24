Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5319392 : forall s : real -> Prop, forall l : real, (has_sup s l) = ((~ (s = (@EMPTY real))) /\ ((forall x : real, (@IN real x s) -> real_le x l) /\ (forall c : real, (real_lt c l) -> exists x : real, (@IN real x s) /\ (real_lt c x)))).
