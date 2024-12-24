Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6970185 : forall {A : Type'}, forall f : A -> nat, forall u : A -> Prop, forall v : A -> Prop, ((@FINITE A v) /\ (forall x : A, ((@IN A x u) /\ (~ (@IN A x v))) -> (f x) = (NUMERAL 0))) -> (@nsum A (@UNION A u v) f) = (@nsum A v f).
