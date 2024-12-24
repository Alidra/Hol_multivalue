Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3270115 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, (@DIFF A (@DIFF A s t) t) = (@DIFF A s t).
