Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1634773 : forall d : real, (real_lt (real_of_num (NUMERAL 0)) d) -> exists e : real, (real_lt (real_of_num (NUMERAL 0)) e) /\ (real_lt e d).
