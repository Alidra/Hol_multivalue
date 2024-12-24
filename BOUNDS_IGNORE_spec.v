Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1262185 : forall P : nat -> nat, forall Q : nat -> nat, (exists B : nat, forall i : nat, Peano.le (P i) (Nat.add (Q i) B)) = (exists B : nat, exists N : nat, forall i : nat, (Peano.le N i) -> Peano.le (P i) (Nat.add (Q i) B)).
