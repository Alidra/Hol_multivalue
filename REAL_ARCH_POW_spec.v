Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1706981 : forall x : real, forall y : real, (real_lt (real_of_num (NUMERAL (BIT1 0))) x) -> exists n : nat, real_lt y (real_pow x n).
