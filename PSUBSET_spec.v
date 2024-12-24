Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3195125 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@PSUBSET A s t) = ((@SUBSET A s t) /\ (~ (s = t))).
