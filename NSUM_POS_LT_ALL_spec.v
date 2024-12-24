Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6960118 : forall {A : Type'}, forall s : A -> Prop, forall f : A -> nat, ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ (forall i : A, (@IN A i s) -> Peano.lt (NUMERAL 0) (f i)))) -> Peano.lt (NUMERAL 0) (@nsum A s f).
