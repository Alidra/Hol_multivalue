Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307068 : (forall m : nat, forall n : nat, (int_gt (int_of_num m) (int_of_num n)) = (Peano.gt m n)) /\ ((forall m : nat, forall n : nat, (int_le (int_of_num m) (int_of_num n)) = (Peano.le m n)) /\ ((forall m : nat, forall n : nat, (int_lt (int_of_num m) (int_of_num n)) = (Peano.lt m n)) /\ ((forall m : nat, forall n : nat, (int_max (int_of_num m) (int_of_num n)) = (int_of_num (Nat.max m n))) /\ ((forall m : nat, forall n : nat, (int_min (int_of_num m) (int_of_num n)) = (int_of_num (Nat.min m n))) /\ ((forall m : nat, forall n : nat, (int_add (int_of_num m) (int_of_num n)) = (int_of_num (Nat.add m n))) /\ ((forall m : nat, forall n : nat, (int_mul (int_of_num m) (int_of_num n)) = (int_of_num (Nat.mul m n))) /\ (forall x : nat, forall n : nat, (int_pow (int_of_num x) n) = (int_of_num (Nat.pow x n))))))))).
