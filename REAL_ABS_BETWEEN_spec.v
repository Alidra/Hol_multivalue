Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1539149 : forall x : real, forall y : real, forall d : real, ((real_lt (real_of_num (NUMERAL 0)) d) /\ ((real_lt (real_sub x d) y) /\ (real_lt y (real_add x d)))) = (real_lt (real_abs (real_sub y x)) d).
