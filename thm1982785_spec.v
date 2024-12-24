Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982785 : forall (x : real), (real_neg x) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x).
