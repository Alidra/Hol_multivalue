Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5782566 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : B -> Prop, ((P (@neutral B op)) /\ (forall x : B, forall y : B, ((P x) /\ (P y)) -> P (op x y))) -> forall f : A -> B, forall s : A -> Prop, (forall x : A, ((@IN A x s) /\ (~ ((f x) = (@neutral B op)))) -> P (f x)) -> P (@iterate B A op s f).
