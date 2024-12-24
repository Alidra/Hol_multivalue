Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2403240 : forall x : int, forall n : int, (int_lt (int_of_num (NUMERAL 0)) n) -> int_lt (rem x n) n.
