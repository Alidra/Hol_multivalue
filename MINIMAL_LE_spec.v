Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem278395 : forall P : nat -> Prop, forall n : nat, (exists r : nat, P r) -> (Peano.le (minimal P) n) = (exists i : nat, (Peano.le i n) /\ (P i)).
