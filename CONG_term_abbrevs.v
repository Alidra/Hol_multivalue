Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : int) (x1 : int) := forall y0 : int, ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term6 (x0 : int) := fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1)).
Definition term5 (x0 : int) := fun y0 : int => forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term22 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1))) x1.
Definition term10 := fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2)).
Definition term9 := fun y0 : int => forall y1 : int, forall y2 : int, ((rem y0 y2) = (rem y1 y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = (@eq2 int (int_of_num y0) (int_of_num y1) (int_mod (int_of_num y2)))) x0.
Definition term39 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term33 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@eq2 nat x0 x1 (num_mod x2)).
Definition term35 (x0 : nat) (x1 : nat) := fun y0 : nat => (@eq2 nat x0 x1 (num_mod y0)) = ((Nat.modulo x0 y0) = (Nat.modulo x1 y0)).
Definition term21 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2))) x0.
Definition term14 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term23 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0))) x2.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (@eq2 nat x0 x1 (num_mod y0)) = (@eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0)))) x2.
Definition term2 (x0 : int) (x1 : int) := fun y0 : int => (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0)).
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = (@eq2 int (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1)))) x1.
Definition term4 (x0 : int) (x1 : int) := forall y0 : int, (@eq2 int x0 x1 (int_mod y0)) = ((rem x0 y0) = (rem x1 y0)).
Definition term1 (x0 : int) (x1 : int) := fun y0 : int => ((rem x0 y0) = (rem x1 y0)) = (@eq2 int x0 x1 (int_mod y0)).
Definition term27 (x0 : nat) (x1 : nat) := forall y0 : nat, (@eq2 nat x0 x1 (num_mod y0)) = (@eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0))).
Definition term19 (x0 : nat) (x1 : nat) := rem (int_of_num x0) (int_of_num x1).
Definition term44 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = ((Nat.modulo y0 y2) = (Nat.modulo y1 y2)).
Definition term42 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = ((Nat.modulo x0 y1) = (Nat.modulo y0 y1)).
Definition term25 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = (@eq2 int (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1))).
Definition term20 (x0 : nat) (x1 : nat) := int_of_num (Nat.modulo x0 x1).
Definition term38 := forall y0 : nat, True.
Definition term12 := forall y0 : int, forall y1 : int, forall y2 : int, (@eq2 int y0 y1 (int_mod y2)) = ((rem y0 y2) = (rem y1 y2)).
Definition term11 := forall y0 : int, forall y1 : int, forall y2 : int, ((rem y0 y2) = (rem y1 y2)) = (@eq2 int y0 y1 (int_mod y2)).
Definition term8 (x0 : int) := forall y0 : int, forall y1 : int, (@eq2 int x0 y0 (int_mod y1)) = ((rem x0 y1) = (rem y0 y1)).
Definition term7 (x0 : int) := forall y0 : int, forall y1 : int, ((rem x0 y1) = (rem y0 y1)) = (@eq2 int x0 y0 (int_mod y1)).
Definition term36 := fun y0 : nat => True.
Definition term37 (x0 : nat) (x1 : nat) := forall y0 : nat, (@eq2 nat x0 x1 (num_mod y0)) = ((Nat.modulo x0 y0) = (Nat.modulo x1 y0)).
Definition term17 (x0 : nat) := forall y0 : nat, (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0)).
Definition term0 (x0 : int) (x1 : int) (x2 : int) := @eq2 int x0 x1 (int_mod x2).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 nat x0 x1 (num_mod x2).
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (rem (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.modulo y0 y1))) x0.
Definition term13 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => (rem (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.modulo x0 y0))) x1.
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((Nat.modulo x0 x2) = (Nat.modulo x1 x2)).
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num x2)).
Definition term31 (x0 : nat) (x1 : nat) := @eq int (rem (int_of_num x0) (int_of_num x1)).
Definition term40 (x0 : Prop) := forall y0 : nat, x0.
Definition term15 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
Definition term32 (x0 : nat) (x1 : nat) := @eq int (int_of_num (Nat.modulo x0 x1)).
Definition term41 (x0 : nat) := fun y0 : nat => forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = ((Nat.modulo x0 y1) = (Nat.modulo y0 y1)).
Definition term43 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = ((Nat.modulo y0 y2) = (Nat.modulo y1 y2)).
