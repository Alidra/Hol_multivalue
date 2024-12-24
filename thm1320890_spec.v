Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1320890 : forall x : hreal, (hreal_mul (hreal_of_num (NUMERAL (BIT1 0))) x) = x.
