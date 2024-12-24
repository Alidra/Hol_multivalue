Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3291085 : forall {A : Type'}, forall s : A -> Prop, forall t : A -> Prop, forall x : A, (@DIFF A (@INSERT A x s) t) = (@COND (A -> Prop) (@IN A x t) (@DIFF A s t) (@INSERT A x (@DIFF A s t))).
