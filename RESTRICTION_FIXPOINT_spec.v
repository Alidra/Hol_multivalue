Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4389660 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, ((@RESTRICTION A B s f) = f) = (@IN (A -> B) f (@EXTENSIONAL A B s)).
