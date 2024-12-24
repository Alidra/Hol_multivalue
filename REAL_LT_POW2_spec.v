Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1642681 : forall n : nat, real_lt (real_of_num (NUMERAL 0)) (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) n).
