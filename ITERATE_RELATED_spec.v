Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5783455 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall R : B -> B -> Prop, ((R (@neutral B op) (@neutral B op)) /\ (forall x1 : B, forall y1 : B, forall x2 : B, forall y2 : B, ((R x1 x2) /\ (R y1 y2)) -> R (op x1 y1) (op x2 y2))) -> forall f : A -> B, forall g : A -> B, forall s : A -> Prop, ((@FINITE A s) /\ (forall x : A, (@IN A x s) -> R (f x) (g x))) -> R (@iterate B A op s f) (@iterate B A op s g).
