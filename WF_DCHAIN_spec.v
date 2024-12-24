Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem316637 : forall {A : Type'} (lt2 : A -> A -> Prop), (@WF A lt2) = (~ (exists s : nat -> A, forall n : nat, lt2 (s (S n)) (s n))).
