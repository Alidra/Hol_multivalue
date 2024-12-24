Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483523 : forall (y : real) (x : real), (real_le x y) = (real_ge (real_sub y x) (real_of_num (NUMERAL 0))).
