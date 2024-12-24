Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483519 : forall (x : real) (y : real), (real_sub x y) = (real_add x (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y)).
