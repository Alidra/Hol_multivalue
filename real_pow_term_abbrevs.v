Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : real) := forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0)).
Definition term1 (x0 : real) := ((real_pow x0 (NUMERAL 0)) = (real_of_num (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (real_pow x0 (S y0)) = (real_mul x0 (real_pow x0 y0))).
