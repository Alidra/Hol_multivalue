Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308188 : forall x : int, forall n : nat, (int_le (int_of_num (NUMERAL 0)) x) -> int_le (int_add (int_of_num (NUMERAL (BIT1 0))) (int_mul (int_of_num n) x)) (int_pow (int_add (int_of_num (NUMERAL (BIT1 0))) x) n).
