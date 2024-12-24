Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = (@eq2 int (int_of_num y0) (int_of_num y1) (int_mod (int_of_num y2)))) x0.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@eq2 nat x0 x1 (num_mod y0)) = (@eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0)))) x2.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = (@eq2 int (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1)))) x1.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (@eq2 nat x0 x1 (num_mod y0)) = (@eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0))).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = (@eq2 int (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1))).
