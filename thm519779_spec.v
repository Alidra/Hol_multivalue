Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem519779 : (Peano.le 0 0) /\ ((forall n : nat, (Peano.le (Nat.add n n) 0) = (Peano.le n 0)) /\ ((forall n : nat, ~ (Peano.le (S (Nat.add n n)) 0)) /\ ((forall n : nat, Peano.le 0 (Nat.add n n)) /\ ((forall n : nat, Peano.le 0 (S (Nat.add n n))) /\ ((forall m : nat, forall n : nat, (Peano.le (Nat.add m m) (Nat.add n n)) = (Peano.le m n)) /\ ((forall m : nat, forall n : nat, (Peano.le (Nat.add m m) (S (Nat.add n n))) = (Peano.le m n)) /\ ((forall m : nat, forall n : nat, (Peano.le (S (Nat.add m m)) (Nat.add n n)) = (Peano.lt m n)) /\ (forall m : nat, forall n : nat, (Peano.le (S (Nat.add m m)) (S (Nat.add n n))) = (Peano.le m n))))))))).
