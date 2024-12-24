Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3924614 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A s) /\ (@FINITE A t)) -> Peano.le (@CARD A (@UNION A s t)) (Nat.add (@CARD A s) (@CARD A t)).
