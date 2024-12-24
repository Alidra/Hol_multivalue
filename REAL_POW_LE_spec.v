Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1582434 : forall x : real, forall n : nat, (real_le (real_of_num (NUMERAL 0)) x) -> real_le (real_of_num (NUMERAL 0)) (real_pow x n).
