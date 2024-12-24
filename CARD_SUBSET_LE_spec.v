Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3904518 : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@FINITE A b) /\ ((@SUBSET A a b) /\ (Peano.le (@CARD A b) (@CARD A a)))) -> a = b.
