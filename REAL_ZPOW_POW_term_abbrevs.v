Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : real) (x1 : nat) := @eq real (real_zpow x0 (int_of_num x1)).
Definition term23 (x0 : real) (x1 : nat) := real_inv (real_zpow x0 (int_of_num x1)).
Definition term21 := and (forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)).
Definition term14 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term25 (x0 : real) (x1 : nat) := @eq real (real_zpow x0 (int_neg (int_of_num x1))).
Definition term7 (x0 : real) (x1 : int) := real_zpow x0 (int_neg x1).
Definition term17 := fun y0 : real => True.
Definition term1 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term31 := (forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) /\ (forall y0 : real, forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1))).
Definition term19 := forall y0 : real, True.
Definition term20 (x0 : Prop) := forall y0 : real, x0.
Definition term30 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1)).
Definition term18 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1).
Definition term6 (x0 : real) (x1 : int) := (fun y0 : int => (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0))) x1.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term5 (x0 : real) := forall y0 : int, (real_zpow x0 (int_neg y0)) = (real_inv (real_zpow x0 y0)).
Definition term27 (x0 : real) := fun y0 : nat => (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0)).
Definition term8 (x0 : real) (x1 : int) := real_inv (real_zpow x0 x1).
Definition term13 := forall y0 : nat, True.
Definition term29 := fun y0 : real => forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1)).
Definition term12 := fun y0 : nat => True.
Definition term22 (x0 : real) (x1 : nat) := real_zpow x0 (int_neg (int_of_num x1)).
Definition term11 (x0 : real) := fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term16 := fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1).
Definition term2 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term10 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term28 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0)).
Definition term4 (x0 : real) := (fun y0 : real => forall y1 : int, (real_zpow y0 (int_neg y1)) = (real_inv (real_zpow y0 y1))) x0.
Definition term24 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term3 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term15 (x0 : Prop) := forall y0 : nat, x0.
Definition term26 (x0 : real) (x1 : nat) := @eq real (real_inv (real_pow x0 x1)).
