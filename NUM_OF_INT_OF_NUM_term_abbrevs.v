Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : nat) := @ε nat (fun y0 : nat => (int_of_num y0) = (int_of_num x0)).
Definition term16 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term1 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term3 (x0 : int) := (fun y0 : int => (num_of_int y0) = (@ε nat (fun y1 : nat => (int_of_num y1) = y0))) x0.
Definition term4 (x0 : int) := @ε nat (fun y0 : nat => (int_of_num y0) = x0).
Definition term9 (x0 : nat) := @ε nat (fun y0 : nat => y0 = x0).
Definition term12 := fun y0 : nat => (num_of_int (int_of_num y0)) = y0.
Definition term15 := forall y0 : nat, True.
Definition term13 := fun y0 : nat => True.
Definition term11 (x0 : nat) := @eq nat (num_of_int (int_of_num x0)).
Definition term14 := forall y0 : nat, (num_of_int (int_of_num y0)) = y0.
Definition term7 (x0 : nat) := fun y0 : nat => (int_of_num y0) = (int_of_num x0).
Definition term10 (a0 : Type') (x0 : a0) := @ε a0 (fun y0 : a0 => y0 = x0).
Definition term8 (x0 : nat) := fun y0 : nat => y0 = x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term5 (x0 : nat) := num_of_int (int_of_num x0).
Definition term17 (x0 : Prop) := forall y0 : nat, x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
