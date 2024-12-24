Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307555 : forall x : int, (int_le (int_of_num (NUMERAL 0)) x) = (exists y : real, (real_pow y (NUMERAL (BIT0 (BIT1 0)))) = (real_of_int x)).
