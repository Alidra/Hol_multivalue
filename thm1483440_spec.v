Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483440 : forall (a : real) (m : real), (real_add (real_mul a m) m) = (real_mul (real_add a (real_of_num (NUMERAL (BIT1 0)))) m).
