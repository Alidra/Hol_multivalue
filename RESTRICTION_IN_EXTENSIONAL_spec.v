Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4387232 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, @IN (A -> B) (@RESTRICTION A B s f) (@EXTENSIONAL A B s).
