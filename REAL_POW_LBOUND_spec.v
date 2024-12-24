Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1704991 : forall x : real, forall n : nat, (real_le (real_of_num (NUMERAL 0)) x) -> real_le (real_add (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_of_num n) x)) (real_pow (real_add (real_of_num (NUMERAL (BIT1 0))) x) n).
