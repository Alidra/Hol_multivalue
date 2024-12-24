Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4382932 : forall {A B : Type'}, forall s : A -> Prop, forall f : A -> B, (@IN (A -> B) f (@EXTENSIONAL A B s)) = (forall x : A, (~ (@IN A x s)) -> (f x) = (@ARB B)).
