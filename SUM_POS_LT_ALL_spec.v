Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7081142 : forall {A : Type'}, forall s : A -> Prop, forall f : A -> real, ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ (forall i : A, (@IN A i s) -> real_lt (real_of_num (NUMERAL 0)) (f i)))) -> real_lt (real_of_num (NUMERAL 0)) (@sum A s f).
