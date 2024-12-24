Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1278627 : forall x : nadd, nadd_eq (nadd_mul (nadd_of_num (NUMERAL (BIT1 0))) x) x.
