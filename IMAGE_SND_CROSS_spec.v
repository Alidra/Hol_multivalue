Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4357468 : forall {A B : Type'}, forall s : A -> Prop, forall t : B -> Prop, (@IMAGE (prod A B) B (@snd A B) (@CROSS B A s t)) = (@COND (B -> Prop) (s = (@EMPTY A)) (@EMPTY B) t).
