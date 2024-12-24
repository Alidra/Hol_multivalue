Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, (int_le (int_of_num (NUMERAL 0)) y1) -> y0 y1) = (forall y1 : nat, y0 (int_of_num y1))) x0.
Definition term1 (x0 : int -> Prop) := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) -> x0 y0.
Definition term2 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
