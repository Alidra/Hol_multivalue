Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3926921 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall m : nat, forall n : nat, (((@FINITE A s) /\ (Peano.le (@CARD A s) m)) /\ ((@FINITE A t) /\ (Peano.le (@CARD A t) n))) -> (@FINITE A (@UNION A s t)) /\ (Peano.le (@CARD A (@UNION A s t)) (Nat.add m n)).
