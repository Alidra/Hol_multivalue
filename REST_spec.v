Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3204727 : forall {A : Type'}, forall s : A -> Prop, (@REST A s) = (@DELETE A s (@CHOICE A s)).
