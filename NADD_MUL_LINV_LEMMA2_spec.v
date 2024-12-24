Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1302159 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists N : nat, forall n : nat, (Peano.le N n) -> Peano.le (dist (@pair nat nat (Nat.mul (dest_nadd x n) (nadd_rinv x n)) (Nat.mul n n))) (dest_nadd x n).
