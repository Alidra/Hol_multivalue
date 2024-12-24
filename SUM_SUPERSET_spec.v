Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7124972 : forall {A : Type'}, forall f : A -> real, forall u : A -> Prop, forall v : A -> Prop, ((@SUBSET A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (real_of_num (NUMERAL 0)))) -> (@sum A v f) = (@sum A u f).
