Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3070937 : forall (x : int) (h1 : int_le (int_of_num (NUMERAL 0)) x), (int_of_num (num_of_int x)) = x.
