Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5273353 : forall s : real -> Prop, forall y : real, ((~ (s = (@EMPTY real))) /\ (exists b : real, forall x : real, (@IN real x s) -> real_le b x)) -> (real_le y (inf s)) = (forall x : real, (@IN real x s) -> real_le y x).
