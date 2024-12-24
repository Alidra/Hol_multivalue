Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6155069 : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall g : B -> C, forall f : A -> B, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((~ (x = y)) /\ ((f x) = (f y))))) -> (g (f x)) = (@neutral C op))) -> (@iterate C B op (@IMAGE A B f s) g) = (@iterate C A op s (@o A B C g f)).
