Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3599924 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, ((@FINITE A t) /\ (@SUBSET A s t)) -> @FINITE A s.
