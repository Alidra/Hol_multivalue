Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1308984 : forall x : nadd, (~ (nadd_eq x (nadd_of_num (NUMERAL 0)))) -> nadd_eq (nadd_mul (nadd_inv x) x) (nadd_of_num (NUMERAL (BIT1 0))).
