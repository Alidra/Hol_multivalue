Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2835824 : forall x : int, forall n : nat, (int_le (int_of_num (NUMERAL 0)) x) -> (num_of_int (int_pow x n)) = (Nat.pow (num_of_int x) n).
