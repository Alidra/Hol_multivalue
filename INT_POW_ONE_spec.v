Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308876 : forall n : nat, (int_pow (int_of_num (NUMERAL (BIT1 0))) n) = (int_of_num (NUMERAL (BIT1 0))).
