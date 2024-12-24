Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306819 : (forall m : nat, forall n : nat, (real_le (real_of_num m) (real_of_num n)) = (Peano.le m n)) /\ ((forall m : nat, forall n : nat, (real_lt (real_of_num m) (real_of_num n)) = (Peano.lt m n)) /\ ((forall m : nat, forall n : nat, (real_max (real_of_num m) (real_of_num n)) = (real_of_num (Nat.max m n))) /\ ((forall m : nat, forall n : nat, (real_min (real_of_num m) (real_of_num n)) = (real_of_num (Nat.min m n))) /\ ((forall m : nat, forall n : nat, (real_add (real_of_num m) (real_of_num n)) = (real_of_num (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (real_mul (real_of_num m) (real_of_num n)) = (real_of_num (Nat.mul m n))) /\ (forall x : nat, forall n : nat, (real_pow (real_of_num x) n) = (real_of_num (Nat.pow x n)))))))).
