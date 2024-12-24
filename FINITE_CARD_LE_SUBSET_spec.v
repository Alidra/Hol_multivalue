Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3908873 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall n : nat, ((@SUBSET A s t) /\ ((@FINITE A t) /\ (Peano.le (@CARD A t) n))) -> (@FINITE A s) /\ (Peano.le (@CARD A s) n).
