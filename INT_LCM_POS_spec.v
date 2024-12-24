Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2806319 : forall m : int, forall n : int, int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int m n)).
