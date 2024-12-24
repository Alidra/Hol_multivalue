Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1980011 : forall (x : nat) (y : nat), ((real_neg (real_of_num x)) = (real_div (real_neg (real_of_num x)) (real_of_num (NUMERAL (BIT1 0))))) /\ (((DECIMAL x y) = (real_div (real_of_num x) (real_of_num y))) /\ ((real_neg (DECIMAL x y)) = (real_div (real_neg (real_of_num x)) (real_of_num y)))).
