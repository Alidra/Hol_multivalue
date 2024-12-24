Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3227973 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@SUBSET A s t) /\ (@PSUBSET A t u)) -> @PSUBSET A s u.
