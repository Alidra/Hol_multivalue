Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4396253 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@RESTRICTION A B s f) = g) = ((@EXTENSIONAL A B s g) /\ (forall x : A, (@IN A x s) -> (f x) = (g x))).