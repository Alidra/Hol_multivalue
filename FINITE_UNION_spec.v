Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3606772 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@FINITE A (@UNION A s t)) = ((@FINITE A s) /\ (@FINITE A t)).
