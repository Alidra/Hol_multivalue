Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5315196 : forall s : real -> Prop, forall l : real, (has_inf s l) = ((~ (s = (@EMPTY real))) /\ ((forall x : real, (@IN real x s) -> real_le l x) /\ (forall c : real, (real_lt l c) -> exists x : real, (@IN real x s) /\ (real_lt x c)))).
