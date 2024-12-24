Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1944746 : forall x : real, (real_le (real_of_num (NUMERAL 0)) x) = (exists y : real, (real_pow y (NUMERAL (BIT0 (BIT1 0)))) = x).
