Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5171252 : forall s : real -> Prop, forall l : real, forall e : real, ((~ (s = (@EMPTY real))) /\ (forall x : real, (@IN real x s) -> real_le (real_abs (real_sub x l)) e)) -> real_le (real_abs (real_sub (sup s) l)) e.
