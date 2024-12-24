Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) (x1 : int) (x2 : int) := (int_divides x1 x0) /\ (int_divides x1 x2).
Definition term0 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_divides x1 (int_gcd (@pair int int x0 y0))) = ((int_divides x1 x0) /\ (int_divides x1 y0))) x2.
Definition term1 (x0 : int) (x1 : int) (x2 : int) := int_divides x0 (int_gcd (@pair int int x1 x2)).
