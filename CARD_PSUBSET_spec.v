Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3921097 : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@PSUBSET A a b) /\ (@FINITE A b)) -> Peano.lt (@CARD A a) (@CARD A b).
