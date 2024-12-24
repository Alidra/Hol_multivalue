Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1261658 : forall P : nat -> nat -> nat, forall A : nat, forall B : nat, (((P (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall m : nat, forall n : nat, Peano.le (P m n) (Nat.add (Nat.mul A (Nat.add m n)) B))) -> exists B' : nat, forall m : nat, forall n : nat, Peano.le (P m n) (Nat.mul B' (Nat.add m n)).
