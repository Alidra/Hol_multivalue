Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem6016892 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall u : A -> Prop, forall v : A -> Prop, ((@SUBSET A u v) /\ (forall x : A, ((@IN A x v) /\ (~ (@IN A x u))) -> (f x) = (@neutral B op))) -> (@iterate B A op v f) = (@iterate B A op u f).
