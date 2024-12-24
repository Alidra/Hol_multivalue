Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term7 (x0 : int) := forall y0 : int, int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int x0 y0)).
Definition term10 (x0 : int) := (fun y0 : int => ((int_of_num (num_of_int y0)) = y0) = (int_le (int_of_num (NUMERAL 0)) y0)) x0.
Definition term26 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term6 (x0 : int) := (fun y0 : int => forall y1 : int, int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int y0 y1))) x0.
Definition term15 (x0 : nat) (x1 : nat) := num_of_int (int_lcm (@pair int int (int_of_num x0) (int_of_num x1))).
Definition term8 (x0 : int) (x1 : int) := (fun y0 : int => int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int x0 y0))) x1.
Definition term12 (x0 : nat) := forall y0 : nat, (num_lcm (@pair nat nat x0 y0)) = (num_of_int (int_lcm (@pair int int (int_of_num x0) (int_of_num y0)))).
Definition term20 (x0 : nat) (x1 : nat) := int_lcm (@pair int int (int_of_num x0) (int_of_num x1)).
Definition term21 (x0 : nat) (x1 : nat) := int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int (int_of_num x0) (int_of_num x1))).
Definition term5 := forall y0 : int, ((int_of_num (num_of_int y0)) = y0) = (int_le (int_of_num (NUMERAL 0)) y0).
Definition term4 := forall y0 : int, (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0).
Definition term22 (x0 : nat) := fun y0 : nat => (int_of_num (num_lcm (@pair nat nat x0 y0))) = (int_lcm (@pair int int (int_of_num x0) (int_of_num y0))).
Definition term29 := forall y0 : nat, forall y1 : nat, (int_of_num (num_lcm (@pair nat nat y0 y1))) = (int_lcm (@pair int int (int_of_num y0) (int_of_num y1))).
Definition term1 (x0 : int) := int_of_num (num_of_int x0).
Definition term25 := forall y0 : nat, True.
Definition term23 := fun y0 : nat => True.
Definition term16 (x0 : nat) (x1 : nat) := int_of_num (num_lcm (@pair nat nat x0 x1)).
Definition term17 (x0 : nat) (x1 : nat) := int_of_num (num_of_int (int_lcm (@pair int int (int_of_num x0) (int_of_num x1)))).
Definition term24 (x0 : nat) := forall y0 : nat, (int_of_num (num_lcm (@pair nat nat x0 y0))) = (int_lcm (@pair int int (int_of_num x0) (int_of_num y0))).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (num_lcm (@pair nat nat x0 y0)) = (num_of_int (int_lcm (@pair int int (int_of_num x0) (int_of_num y0))))) x1.
Definition term19 (x0 : nat) (x1 : nat) := @eq int (int_of_num (num_of_int (int_lcm (@pair int int (int_of_num x0) (int_of_num x1))))).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (num_lcm (@pair nat nat y0 y1)) = (num_of_int (int_lcm (@pair int int (int_of_num y0) (int_of_num y1))))) x0.
Definition term2 := fun y0 : int => (int_le (int_of_num (NUMERAL 0)) y0) = ((int_of_num (num_of_int y0)) = y0).
Definition term3 := fun y0 : int => ((int_of_num (num_of_int y0)) = y0) = (int_le (int_of_num (NUMERAL 0)) y0).
Definition term9 (x0 : int) (x1 : int) := int_le (int_of_num (NUMERAL 0)) (int_lcm (@pair int int x0 x1)).
Definition term27 (x0 : Prop) := forall y0 : nat, x0.
Definition term28 := fun y0 : nat => forall y1 : nat, (int_of_num (num_lcm (@pair nat nat y0 y1))) = (int_lcm (@pair int int (int_of_num y0) (int_of_num y1))).
Definition term0 (x0 : int) := int_le (int_of_num (NUMERAL 0)) x0.
Definition term14 (x0 : nat) (x1 : nat) := num_lcm (@pair nat nat x0 x1).
Definition term18 (x0 : nat) (x1 : nat) := @eq int (int_of_num (num_lcm (@pair nat nat x0 x1))).
