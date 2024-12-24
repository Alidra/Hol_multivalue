Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3169346 : forall x : real, (real_zpow x (int_of_num (NUMERAL 0))) = (real_of_num (NUMERAL (BIT1 0))).
