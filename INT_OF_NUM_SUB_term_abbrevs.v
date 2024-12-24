Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term10 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term9 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term13 (x0 : nat) (x1 : nat) := @eq real (real_of_int (int_sub (int_of_num x0) (int_of_num x1))).
Definition term14 (x0 : nat) (x1 : nat) := real_of_num (Nat.sub x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.le x0 y0) -> (real_sub (real_of_num y0) (real_of_num x0)) = (real_of_num (Nat.sub y0 x0))) x1.
Definition term18 (x0 : nat) (x1 : nat) := imp (Peano.le x0 x1).
Definition term3 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (real_sub (real_of_num x0) (real_of_num x1)) = (real_of_num (Nat.sub x0 x1)).
Definition term7 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_of_num x1).
Definition term12 (x0 : nat) (x1 : nat) := @eq real (real_sub (real_of_num x0) (real_of_num x1)).
Definition term4 (x0 : nat) := real_of_int (int_of_num x0).
Definition term15 (x0 : nat) (x1 : nat) := real_of_int (int_of_num (Nat.sub x0 x1)).
Definition term16 (x0 : nat) (x1 : nat) := int_sub (int_of_num x0) (int_of_num x1).
Definition term6 (x0 : nat) := real_sub (real_of_int (int_of_num x0)).
Definition term21 := forall y0 : nat, forall y1 : nat, (Peano.le y0 y1) -> (int_sub (int_of_num y1) (int_of_num y0)) = (int_of_num (Nat.sub y1 y0)).
Definition term19 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) -> (int_sub (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.sub x0 x1)).
Definition term5 (x0 : nat) := real_sub (real_of_num x0).
Definition term17 (x0 : nat) (x1 : nat) := int_of_num (Nat.sub x0 x1).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.le y0 y1) -> (real_sub (real_of_num y1) (real_of_num y0)) = (real_of_num (Nat.sub y1 y0))) x0.
Definition term20 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> (int_sub (int_of_num y0) (int_of_num x0)) = (int_of_num (Nat.sub y0 x0)).
Definition term1 (x0 : nat) := forall y0 : nat, (Peano.le x0 y0) -> (real_sub (real_of_num y0) (real_of_num x0)) = (real_of_num (Nat.sub y0 x0)).
Definition term8 (x0 : nat) (x1 : nat) := real_sub (real_of_int (int_of_num x0)) (real_of_int (int_of_num x1)).
Definition term11 (x0 : nat) (x1 : nat) := real_of_int (int_sub (int_of_num x0) (int_of_num x1)).
