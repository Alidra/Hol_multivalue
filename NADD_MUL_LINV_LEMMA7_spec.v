Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1305777 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists B : nat, exists N : nat, forall m : nat, forall n : nat, ((Peano.le N m) /\ (Peano.le N n)) -> Peano.le (dist (@pair nat nat (Nat.mul m (nadd_rinv x n)) (Nat.mul n (nadd_rinv x m)))) (Nat.mul B (Nat.add m n)).
