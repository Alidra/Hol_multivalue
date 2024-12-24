Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3235655 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@SUBSET A s t) = ((@UNION A s t) = t).
