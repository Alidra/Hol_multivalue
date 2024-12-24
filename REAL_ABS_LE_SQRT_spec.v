Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1977057 : forall x : real, forall y : real, real_le (real_abs (real_sub (sqrt x) (sqrt y))) (sqrt (real_mul (real_of_num (NUMERAL (BIT0 (BIT1 0)))) (real_abs (real_sub x y)))).
