Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4355951 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@IMAGE (prod A B) A (@fst A B) (@CROSS B A s t)) = (@COND (A -> Prop) (t = (@EMPTY B)) (@EMPTY A) s).
