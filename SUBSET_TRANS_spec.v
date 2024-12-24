Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3217353 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall u : A -> Prop, ((@SUBSET A s t) /\ (@SUBSET A t u)) -> @SUBSET A s u.
