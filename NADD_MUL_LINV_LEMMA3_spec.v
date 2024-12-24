Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1302302 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists N : nat, forall m : nat, forall n : nat, (Peano.le N n) -> Peano.le (dist (@pair nat nat (Nat.mul m (Nat.mul (dest_nadd x m) (Nat.mul (dest_nadd x n) (nadd_rinv x n)))) (Nat.mul m (Nat.mul (dest_nadd x m) (Nat.mul n n))))) (Nat.mul m (Nat.mul (dest_nadd x m) (dest_nadd x n))).
