Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5804540 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (@neutral B op)) -> (@iterate B A op s f) = (@neutral B op).
