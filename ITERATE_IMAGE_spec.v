Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5942955 : forall {A B C : Type'}, forall op : C -> C -> C, (@monoidal C op) -> forall f : A -> B, forall g : B -> C, forall s : A -> Prop, (forall x : A, forall y : A, ((@IN A x s) /\ ((@IN A y s) /\ ((f x) = (f y)))) -> x = y) -> (@iterate C B op (@IMAGE A B f s) g) = (@iterate C A op s (@o A B C g f)).
