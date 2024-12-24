Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302493 : forall {A : Type'}, forall P : nat -> A -> Prop, forall R : nat -> A -> A -> Prop, ((exists a : A, P (NUMERAL 0) a) /\ (forall n : nat, forall x : A, (P n x) -> exists y : A, (P (S n) y) /\ (R n x y))) -> exists f : nat -> A, (forall n : nat, P n (f n)) /\ (forall n : nat, R n (f n) (f (S n))).
