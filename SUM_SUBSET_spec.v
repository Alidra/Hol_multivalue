Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7173279 : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> real, ((@FINITE A u) /\ ((@FINITE A v) /\ ((forall x : A, (@IN A x (@DIFF A u v)) -> real_le (f x) (real_of_num (NUMERAL 0))) /\ (forall x : A, (@IN A x (@DIFF A v u)) -> real_le (real_of_num (NUMERAL 0)) (f x))))) -> real_le (@sum A u f) (@sum A v f).
