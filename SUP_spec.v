Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5136700 : forall s : real -> Prop, ((~ (s = (@EMPTY real))) /\ (exists b : real, forall x : real, (@IN real x s) -> real_le x b)) -> (forall x : real, (@IN real x s) -> real_le x (sup s)) /\ (forall b : real, (forall x : real, (@IN real x s) -> real_le x b) -> real_le (sup s) b).
