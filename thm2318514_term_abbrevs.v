Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) := (fun y0 : int => (real_of_int (int_abs y0)) = (real_abs (real_of_int y0))) x0.