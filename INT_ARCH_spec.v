Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2350530 : forall x : int, forall d : int, (~ (d = (int_of_num (NUMERAL 0)))) -> exists c : int, int_lt x (int_mul c d).
