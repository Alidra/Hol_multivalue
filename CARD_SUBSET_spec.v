Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3902682 : forall {A : Type'}, forall a : A -> Prop, forall b : A -> Prop, ((@SUBSET A a b) /\ (@FINITE A b)) -> Peano.le (@CARD A a) (@CARD A b).
