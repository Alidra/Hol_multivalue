Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300082 : forall x : int, forall y : int, forall d : int, ((int_lt (int_of_num (NUMERAL 0)) d) /\ ((int_lt (int_sub x d) y) /\ (int_lt y (int_add x d)))) = (int_lt (int_abs (int_sub y x)) d).
