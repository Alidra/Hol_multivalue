Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5266204 : forall s : real -> Prop, ((~ (s = (@EMPTY real))) /\ (exists B : real, forall x : real, (@IN real x s) -> real_le (real_abs x) B)) -> ((sup s) = (inf s)) = (exists a : real, s = (@INSERT real a (@EMPTY real))).
