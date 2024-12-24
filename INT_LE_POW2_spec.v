Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2303055 : forall n : nat, int_le (int_of_num (NUMERAL (BIT1 0))) (int_pow (int_of_num (NUMERAL (BIT0 (BIT1 0)))) n).
