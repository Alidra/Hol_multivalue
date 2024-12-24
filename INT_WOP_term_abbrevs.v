Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : int -> Prop) := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ ((x0 y0) /\ (forall y1 : int, ((int_le (int_of_num (NUMERAL 0)) y1) /\ (x0 y1)) -> int_le y0 y1)).
Definition term0 (x0 : int -> Prop) := exists y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) /\ (x0 y0).
