Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5809499 : forall {A B : Type'}, forall op : B -> B -> B, (@monoidal B op) -> forall P : B -> Prop, (forall x : B, forall y : B, ((P x) /\ (P y)) -> P (op x y)) -> forall f : A -> B, forall s : A -> Prop, ((@FINITE A s) /\ ((~ (s = (@EMPTY A))) /\ (forall x : A, (@IN A x s) -> P (f x)))) -> P (@iterate B A op s f).
