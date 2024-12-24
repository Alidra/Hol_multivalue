Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1636366 : forall d1 : real, forall d2 : real, ((real_lt (real_of_num (NUMERAL 0)) d1) /\ (real_lt (real_of_num (NUMERAL 0)) d2)) -> exists e : real, (real_lt (real_of_num (NUMERAL 0)) e) /\ ((real_lt e d1) /\ (real_lt e d2)).
