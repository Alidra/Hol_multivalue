Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7136923 : forall {A : Type'}, forall s : A -> Prop, forall f : A -> real, forall b : real, ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ (forall x : A, (@IN A x s) -> real_le (f x) (real_div b (real_of_num (@CARD A s)))))) -> real_le (@sum A s f) b.