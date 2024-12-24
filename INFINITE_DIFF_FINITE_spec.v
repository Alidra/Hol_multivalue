Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3632103 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@INFINITE A s) /\ (@FINITE A t)) -> @INFINITE A (@DIFF A s t).
