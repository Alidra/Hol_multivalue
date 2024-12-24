Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1301912 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> exists A : nat, exists B : nat, forall n : nat, Peano.le (nadd_rinv x n) (Nat.add (Nat.mul A n) B).
