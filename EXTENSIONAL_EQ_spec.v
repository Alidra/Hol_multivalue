Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4385509 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, ((@IN (A -> B) f (@EXTENSIONAL A B s)) /\ ((@IN (A -> B) g (@EXTENSIONAL A B s)) /\ (forall x : A, (@IN A x s) -> (f x) = (g x)))) -> f = g.
