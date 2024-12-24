Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (num_mod y0 y1 y2) = (int_mod (int_of_num y0) (int_of_num y1) (int_of_num y2))) x0.
Definition term20 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (@eq2 nat x0 x1 (num_mod x2)).
Definition term15 (x0 : nat) := int_mod (int_of_num x0).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (num_mod x0 y0 y1) = (int_mod (int_of_num x0) (int_of_num y0) (int_of_num y1))) x1.
Definition term18 (x0 : nat) (x1 : nat) := forall y0 : nat, (@eq2 nat x0 x1 (num_mod y0)) = (@eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0))).
Definition term16 (x0 : nat) (x1 : nat) := fun y0 : nat => (@eq2 nat x0 x1 (num_mod y0)) = (@eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num y0))).
Definition term10 (a0 : Type') (x0 : type1402 a0) (x1 : a0) (x2 : a0) := (fun y0 : a0 => (@eq2 a0 x1 y0 x0) = (x0 x1 y0)) x2.
Definition term8 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := (fun y0 : a0 => forall y1 : a0, (@eq2 a0 y0 y1 x0) = (x0 y0 y1)) x1.
Definition term25 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = (@eq2 int (int_of_num y0) (int_of_num y1) (int_mod (int_of_num y2))).
Definition term23 (x0 : nat) := forall y0 : nat, forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = (@eq2 int (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1))).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (num_mod x0 y0 y1) = (int_mod (int_of_num x0) (int_of_num y0) (int_of_num y1)).
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := int_mod (int_of_num x0) (int_of_num x1) (int_of_num x2).
Definition term19 := forall y0 : nat, True.
Definition term17 := fun y0 : nat => True.
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (num_mod x0 x1 y0) = (int_mod (int_of_num x0) (int_of_num x1) (int_of_num y0))) x2.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 nat x0 x1 (num_mod x2).
Definition term7 (a0 : Type') (x0 : type1402 a0) := forall y0 : a0, forall y1 : a0, (@eq2 a0 y0 y1 x0) = (x0 y0 y1).
Definition term9 (a0 : Type') (x0 : type1402 a0) (x1 : a0) := forall y0 : a0, (@eq2 a0 x1 y0 x0) = (x0 x1 y0).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := @eq2 int (int_of_num x0) (int_of_num x1) (int_mod (int_of_num x2)).
Definition term21 (x0 : Prop) := forall y0 : nat, x0.
Definition term6 (a0 : Type') (x0 : type1402 a0) := (fun y0 : type1402 a0 => forall y1 : a0, forall y2 : a0, (@eq2 a0 y1 y2 y0) = (y0 y1 y2)) x0.
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (num_mod x0 x1 y0) = (int_mod (int_of_num x0) (int_of_num x1) (int_of_num y0)).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (int_mod (int_of_num x0) (int_of_num x1) (int_of_num x2)).
Definition term22 (x0 : nat) := fun y0 : nat => forall y1 : nat, (@eq2 nat x0 y0 (num_mod y1)) = (@eq2 int (int_of_num x0) (int_of_num y0) (int_mod (int_of_num y1))).
Definition term24 := fun y0 : nat => forall y1 : nat, forall y2 : nat, (@eq2 nat y0 y1 (num_mod y2)) = (@eq2 int (int_of_num y0) (int_of_num y1) (int_mod (int_of_num y2))).
