Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5985778 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, (forall x : A, (@IN A x s) -> (f x) = (g x)) -> (@iterate B A op s f) = (@iterate B A op s g).
