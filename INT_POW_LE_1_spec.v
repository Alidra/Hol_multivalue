Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308414 : forall n : nat, forall x : int, (int_le (int_of_num (NUMERAL (BIT1 0))) x) -> int_le (int_of_num (NUMERAL (BIT1 0))) (int_pow x n).
