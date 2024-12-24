Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem5470571 : forall m : nat, forall n : nat, forall p : nat, (dotdot (Nat.add m p) (Nat.add n p)) = (@IMAGE nat nat (fun i : nat => Nat.add i p) (dotdot m n)).
