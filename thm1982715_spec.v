Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982715 : forall (a : real) (m : real), (real_add m (real_mul a m)) = (real_mul (real_add a (real_of_num (NUMERAL (BIT1 0)))) m).
