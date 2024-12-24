Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308223 : forall x : int, forall n : nat, (int_le (int_of_num (NUMERAL 0)) x) -> int_le (int_of_num (NUMERAL 0)) (int_pow x n).
