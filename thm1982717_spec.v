Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982717 : forall (m : real), (real_add m m) = (real_mul (real_add (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL (BIT1 0)))) m).
