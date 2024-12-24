Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2304131 : forall x : int, forall y : int, forall z : int, ((int_lt (int_of_num (NUMERAL 0)) x) /\ (int_lt (int_mul x y) (int_mul x z))) -> int_lt y z.
