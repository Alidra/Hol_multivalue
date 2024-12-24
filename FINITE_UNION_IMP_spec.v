Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3606091 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A s) /\ (@FINITE A t)) -> @FINITE A (@UNION A s t).
