Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1306676 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> forall N : nat, exists A : nat, exists B : nat, forall m : nat, forall n : nat, (Peano.le m N) -> Peano.le (dist (@pair nat nat (Nat.mul m (nadd_rinv x n)) (Nat.mul n (nadd_rinv x m)))) (Nat.add (Nat.mul A n) B).
