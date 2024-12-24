Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1643457 : forall n : nat, real_le (real_of_num (NUMERAL (BIT1 0))) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) n).
