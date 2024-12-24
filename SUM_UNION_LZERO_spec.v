Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7132219 : forall {A : Type'}, forall f : A -> real, forall u : A -> Prop, forall v : A -> Prop, ((@FINITE A v) /\ (forall x : A, ((@IN A x u) /\ (~ (@IN A x v))) -> (f x) = (real_of_num (NUMERAL 0)))) -> (@sum A (@UNION A u v) f) = (@sum A v f).
