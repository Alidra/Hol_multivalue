Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : real) := @eq Prop (exists y0 : nat, (real_abs x0) = (real_of_num y0)).
Definition term0 (x0 : real) := (fun y0 : real => (integer y0) = (exists y1 : nat, (real_abs y0) = (real_of_num y1))) x0.
Definition term1 (x0 : real) := exists y0 : nat, (real_abs x0) = (real_of_num y0).
Definition term4 (x0 : real) := exists y0 : nat, (x0 = (real_of_num y0)) \/ (x0 = (real_neg (real_of_num y0))).
Definition term2 (x0 : real) := @eq Prop (integer x0).
