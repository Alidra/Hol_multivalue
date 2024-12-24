Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300732 : forall x : int, forall y : int, (int_lt (int_abs (int_sub x y)) (int_abs y)) -> ~ (x = (int_of_num (NUMERAL 0))).
