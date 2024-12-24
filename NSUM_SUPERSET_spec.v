Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6962131 : forall {A : Type'}, forall f : A -> nat, forall u : A -> Prop, forall v : A -> Prop, ((@SUBSET A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (NUMERAL 0))) -> (@nsum A v f) = (@nsum A u f).
