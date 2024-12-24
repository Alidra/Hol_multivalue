Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5166579 : forall s : real -> Prop, forall a : real, ((~ (s = (@EMPTY real))) /\ (forall x : real, (@IN real x s) -> real_le (real_abs x) a)) -> real_le (real_abs (sup s)) a.
