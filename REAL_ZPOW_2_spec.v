Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3169425 : forall x : real, (real_zpow x (int_of_num (NUMERAL (BIT0 (BIT1 0))))) = (real_mul x x).
