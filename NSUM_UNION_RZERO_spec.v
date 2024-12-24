Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6967615 : forall {A : Type'}, forall f : A -> nat, forall u : A -> Prop, forall v : A -> Prop, ((@FINITE A u) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (NUMERAL 0))) -> (@nsum A (@UNION A u v) f) = (@nsum A u f).
