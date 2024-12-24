Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7129616 : forall {A : Type'}, forall f : A -> real, forall u : A -> Prop, forall v : A -> Prop, ((@FINITE A u) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (real_of_num (NUMERAL 0)))) -> (@sum A (@UNION A u v) f) = (@sum A u f).
