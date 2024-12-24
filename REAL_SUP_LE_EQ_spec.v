Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5188259 : forall s : real -> Prop, forall y : real, ((~ (s = (@EMPTY real))) /\ (exists b : real, forall x : real, (@IN real x s) -> real_le x b)) -> (real_le (sup s) y) = (forall x : real, (@IN real x s) -> real_le x y).
