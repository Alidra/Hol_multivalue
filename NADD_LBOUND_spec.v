Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1300501 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists A : nat, exists N : nat, forall n : nat, (Peano.le N n) -> Peano.le n (Nat.mul A (dest_nadd x n)).
