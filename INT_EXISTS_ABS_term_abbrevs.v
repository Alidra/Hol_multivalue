Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term64 (x0 : int -> Prop) (x1 : int) := ~ ((fun y0 : int => x0 (int_abs y0)) x1).
Definition term19 := @eq Prop (~ False).
Definition term8 (x0 : Prop) := fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0)).
Definition term17 (x0 : Prop) := @eq Prop (False = x0).
Definition term49 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => ~ (x0 y1)) (int_abs y0).
Definition term16 (x0 : Prop) := ~ (~ x0).
Definition term3 (a0 : Type') (x0 : a0 -> Prop) := (fun y0 : a0 -> Prop => (~ (exists y1 : a0, y0 y1)) = (forall y1 : a0, ~ (y0 y1))) x0.
Definition term14 (x0 : Prop) := @eq Prop (True = x0).
Definition term63 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : int, x0 (int_abs y0))).
Definition term62 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : int, (fun y1 : int => x0 (int_abs y1)) y0)).
Definition term34 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : nat, x0 (int_of_num y0))).
Definition term33 (x0 : int -> Prop) := @eq Prop (~ (exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0)).
Definition term0 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : nat, y0 (int_of_num y1)) = (forall y1 : int, y0 (int_abs y1))) x0.
Definition term12 (x0 : Prop) (x1 : Prop) := @eq Prop ((x0 = x1) = ((~ x0) = (~ x1))).
Definition term44 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : int => ~ (x0 y1)) (int_of_num y0).
Definition term42 (x0 : int -> Prop) := fun y0 : int => ~ (x0 y0).
Definition term21 (x0 : int -> Prop) := exists y0 : int, x0 (int_abs y0).
Definition term43 (x0 : int -> Prop) (x1 : nat) := (fun y0 : int => ~ (x0 y0)) (int_of_num x1).
Definition term52 (x0 : int -> Prop) := @eq Prop (forall y0 : int, ~ (x0 (int_abs y0))).
Definition term29 (x0 : int -> Prop) (x1 : nat) := (fun y0 : nat => x0 (int_of_num y0)) x1.
Definition term47 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => ~ (x0 y0)) (int_abs x1).
Definition term20 (x0 : int -> Prop) := exists y0 : nat, x0 (int_of_num y0).
Definition term9 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1.
Definition term13 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) False.
Definition term38 (x0 : int -> Prop) := fun y0 : nat => ~ (x0 (int_of_num y0)).
Definition term23 (x0 : int -> Prop) := ~ (exists y0 : int, x0 (int_abs y0)).
Definition term45 (x0 : int -> Prop) := @eq Prop (forall y0 : nat, (fun y1 : int => ~ (x0 y1)) (int_of_num y0)).
Definition term22 (x0 : int -> Prop) := ~ (exists y0 : nat, x0 (int_of_num y0)).
Definition term54 (x0 : int -> Prop) := forall y0 : int, ~ (x0 y0).
Definition term31 (x0 : int -> Prop) := fun y0 : nat => (fun y1 : nat => x0 (int_of_num y1)) y0.
Definition term55 (x0 : int -> Prop) := ~ (exists y0 : int, (fun y1 : int => x0 (int_abs y1)) y0).
Definition term51 (x0 : int -> Prop) := forall y0 : int, ~ (x0 (int_abs y0)).
Definition term5 (a0 : Type') (x0 : a0 -> Prop) := forall y0 : a0, ~ (x0 y0).
Definition term58 (x0 : int -> Prop) (x1 : int) := (fun y0 : int => x0 (int_abs y0)) x1.
Definition term18 (x0 : Prop) := @eq Prop (~ x0).
Definition term25 (x0 : nat -> Prop) := forall y0 : nat, ~ (x0 y0).
Definition term53 (x0 : int -> Prop) := ~ (exists y0 : int, x0 y0).
Definition term4 (a0 : Type') (x0 : a0 -> Prop) := ~ (exists y0 : a0, x0 y0).
Definition term26 (x0 : int -> Prop) := ~ (exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term11 (x0 : Prop) (x1 : Prop) := @eq Prop ((fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) x1).
Definition term15 := @eq Prop (~ True).
Definition term7 (x0 : Prop) := (x0 = True) \/ (x0 = False).
Definition term65 (x0 : int -> Prop) := fun y0 : int => ~ ((fun y1 : int => x0 (int_abs y1)) y0).
Definition term41 (x0 : int -> Prop) := forall y0 : int, (fun y1 : int => ~ (x0 y1)) (int_abs y0).
Definition term61 (x0 : int -> Prop) := exists y0 : int, (fun y1 : int => x0 (int_abs y1)) y0.
Definition term40 (x0 : int -> Prop) := forall y0 : nat, (fun y1 : int => ~ (x0 y1)) (int_of_num y0).
Definition term27 (x0 : int -> Prop) := forall y0 : nat, ~ ((fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term1 (x0 : int -> Prop) := forall y0 : nat, x0 (int_of_num y0).
Definition term60 (x0 : int -> Prop) := fun y0 : int => (fun y1 : int => x0 (int_abs y1)) y0.
Definition term59 (x0 : int -> Prop) (x1 : int) := x0 (int_abs x1).
Definition term39 (x0 : int -> Prop) := forall y0 : nat, ~ (x0 (int_of_num y0)).
Definition term50 (x0 : int -> Prop) := fun y0 : int => ~ (x0 (int_abs y0)).
Definition term46 (x0 : int -> Prop) := @eq Prop (forall y0 : nat, ~ (x0 (int_of_num y0))).
Definition term66 := forall y0 : int -> Prop, (exists y1 : nat, y0 (int_of_num y1)) = (exists y1 : int, y0 (int_abs y1)).
Definition term48 (x0 : int -> Prop) (x1 : int) := ~ (x0 (int_abs x1)).
Definition term36 (x0 : int -> Prop) (x1 : nat) := ~ (x0 (int_of_num x1)).
Definition term57 (x0 : int -> Prop) := fun y0 : int => x0 (int_abs y0).
Definition term28 (x0 : int -> Prop) := fun y0 : nat => x0 (int_of_num y0).
Definition term35 (x0 : int -> Prop) (x1 : nat) := ~ ((fun y0 : nat => x0 (int_of_num y0)) x1).
Definition term2 (x0 : int -> Prop) := forall y0 : int, x0 (int_abs y0).
Definition term30 (x0 : int -> Prop) (x1 : nat) := x0 (int_of_num x1).
Definition term24 (x0 : nat -> Prop) := ~ (exists y0 : nat, x0 y0).
Definition term37 (x0 : int -> Prop) := fun y0 : nat => ~ ((fun y1 : nat => x0 (int_of_num y1)) y0).
Definition term10 (x0 : Prop) := (fun y0 : Prop => (y0 = x0) = ((~ y0) = (~ x0))) True.
Definition term6 (x0 : Prop) := (fun y0 : Prop => (y0 = True) \/ (y0 = False)) x0.
Definition term32 (x0 : int -> Prop) := exists y0 : nat, (fun y1 : nat => x0 (int_of_num y1)) y0.
Definition term56 (x0 : int -> Prop) := forall y0 : int, ~ ((fun y1 : int => x0 (int_abs y1)) y0).
