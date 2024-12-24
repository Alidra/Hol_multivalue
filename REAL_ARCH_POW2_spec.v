Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1707681 : forall x : real, exists n : nat, real_lt x (real_pow (real_of_num (NUMERAL (BIT0 (BIT1 0)))) n).
