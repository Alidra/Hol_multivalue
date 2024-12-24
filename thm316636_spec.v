Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem316636 : forall {A : Type'} (lt2 : A -> A -> Prop), (exists P : A -> Prop, ~ ((exists x : A, P x) -> exists x : A, (P x) /\ (forall y : A, (lt2 y x) -> ~ (P y)))) = (exists s : nat -> A, forall n : nat, lt2 (s (S n)) (s n)).
