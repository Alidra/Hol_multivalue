Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1302948 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists N : nat, forall m : nat, forall n : nat, ((Peano.le N m) /\ (Peano.le N n)) -> Peano.le (Nat.mul (Nat.mul (dest_nadd x m) (dest_nadd x n)) (dist (@pair nat nat (Nat.mul m (nadd_rinv x n)) (Nat.mul n (nadd_rinv x m))))) (Nat.add (Nat.mul (Nat.mul m n) (dist (@pair nat nat (Nat.mul m (dest_nadd x n)) (Nat.mul n (dest_nadd x m))))) (Nat.mul (Nat.mul (dest_nadd x m) (dest_nadd x n)) (Nat.add m n))).
