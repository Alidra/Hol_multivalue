Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) := exists y0 : int, x0 = (int_mul x1 y0).
Definition term0 (x0 : int) := (fun y0 : int => forall y1 : int, (int_divides y1 y0) = (exists y2 : int, y0 = (int_mul y1 y2))) x0.
Definition term9 (x0 : nat) (x1 : nat) := @eq Prop (num_divides x0 x1).
Definition term11 (x0 : nat) (x1 : nat) := exists y0 : nat, x0 = (Nat.mul x1 y0).
Definition term10 (x0 : nat) (x1 : nat) := @eq Prop (exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0)).
Definition term2 (x0 : int) (x1 : int) := (fun y0 : int => (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1))) x1.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (num_divides y0 y1) = (int_divides (int_of_num y0) (int_of_num y1))) x0.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0))) x1.
Definition term8 (x0 : nat) (x1 : nat) := exists y0 : int, (int_of_num x0) = (int_mul (int_of_num x1) y0).
Definition term5 (x0 : nat) := forall y0 : nat, (num_divides x0 y0) = (int_divides (int_of_num x0) (int_of_num y0)).
Definition term1 (x0 : int) := forall y0 : int, (int_divides y0 x0) = (exists y1 : int, x0 = (int_mul y0 y1)).
Definition term7 (x0 : nat) (x1 : nat) := int_divides (int_of_num x0) (int_of_num x1).
