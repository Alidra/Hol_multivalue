Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5160982 : forall (s : real -> Prop), forall b : real, ((~ (s = (@EMPTY real))) /\ (forall x : real, (@IN real x s) -> real_le x b)) -> real_le (sup s) b.
