Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7006898 : forall {A : Type'}, forall u : A -> Prop, forall v : A -> Prop, forall f : A -> nat, ((@FINITE A u) /\ ((@FINITE A v) /\ (forall x : A, (@IN A x (@DIFF A u v)) -> (f x) = (NUMERAL 0)))) -> Peano.le (@nsum A u f) (@nsum A v f).
