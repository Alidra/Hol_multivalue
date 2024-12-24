Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem117739 : forall P : nat -> Prop, ((exists x : nat, P x) /\ (exists M : nat, forall x : nat, (P x) -> Peano.le x M)) = (exists m : nat, (P m) /\ (forall x : nat, (P x) -> Peano.le x m)).
