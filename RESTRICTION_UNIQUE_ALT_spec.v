Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4398338 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, forall g : A -> B, (f = (@RESTRICTION A B s g)) = ((@EXTENSIONAL A B s f) /\ (forall x : A, (@IN A x s) -> (f x) = (g x))).
