Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@eq2 nat x0 x1 (num_mod y0)) = (@eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0)))) x2.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 nat x0 x1 (num_mod x2).
Definition term2 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num x2)).
