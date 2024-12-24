Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3487336 : forall {A B : Type'}, forall f : A -> B, forall g : (A -> Prop) -> Prop, @SUBSET B (@IMAGE A B f (@INTERS A g)) (@INTERS B (@IMAGE (A -> Prop) (B -> Prop) (@IMAGE A B f) g)).
