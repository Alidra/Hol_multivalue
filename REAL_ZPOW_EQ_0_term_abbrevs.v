Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term49 (x0 : real) (x1 : nat) := @eq real (real_zpow x0 (int_of_num x1)).
Definition term24 (x0 : int -> Prop) := (forall y0 : nat, x0 (int_of_num y0)) /\ (forall y0 : nat, x0 (int_neg (int_of_num y0))).
Definition term6 := real_of_num (NUMERAL 0).
Definition term31 (x0 : real) := forall y0 : int, ((real_zpow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (int_of_num (NUMERAL 0))))).
Definition term28 (x0 : real) (x1 : int) := (fun y0 : int => ((real_zpow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (int_of_num (NUMERAL 0)))))) x1.
Definition term9 := int_of_num (NUMERAL 0).
Definition term72 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term56 (x0 : real) (x1 : nat) := @eq real (real_zpow x0 (int_neg (int_of_num x1))).
Definition term76 := fun y0 : real => True.
Definition term63 := fun y0 : real => (forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y1) = (int_of_num (NUMERAL 0)))))) /\ (forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y1)) = (int_of_num (NUMERAL 0)))))).
Definition term19 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term36 (x0 : real) := fun y0 : nat => (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) (int_of_num y0).
Definition term22 (x0 : int -> Prop) := (fun y0 : int -> Prop => (forall y1 : int, y0 y1) = ((forall y1 : nat, y0 (int_of_num y1)) /\ (forall y1 : nat, y0 (int_neg (int_of_num y1))))) x0.
Definition term77 := forall y0 : real, True.
Definition term78 (x0 : Prop) := forall y0 : real, x0.
Definition term43 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num x1)) = (int_of_num (NUMERAL 0)))).
Definition term8 (x0 : int) := (fun y0 : int => ((int_neg y0) = (int_of_num (NUMERAL 0))) = (y0 = (int_of_num (NUMERAL 0)))) x0.
Definition term64 := forall y0 : real, forall y1 : int, ((real_zpow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0))))).
Definition term17 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1).
Definition term11 := forall y0 : real, forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1)).
Definition term51 (x0 : real) (x1 : nat) := @eq Prop ((real_zpow x0 (int_of_num x1)) = (real_of_num (NUMERAL 0))).
Definition term68 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term33 (x0 : real) := @eq Prop (forall y0 : int, ((real_zpow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (int_of_num (NUMERAL 0)))))).
Definition term18 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_of_num y1)) = (real_pow y0 y1)) x0.
Definition term12 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_zpow y0 (int_neg (int_of_num y1))) = (real_inv (real_pow y0 y1))) x0.
Definition term3 (x0 : real) := (fun y0 : real => forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term14 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0))) x1.
Definition term26 (x0 : real) := (forall y0 : nat, (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) (int_of_num y0)) /\ (forall y0 : nat, (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) (int_neg (int_of_num y0))).
Definition term55 (x0 : real) := and (forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0)))))).
Definition term41 (x0 : real) := and (forall y0 : nat, ((real_zpow x0 (int_of_num y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0)))))).
Definition term67 (x0 : nat) := ~ ((int_of_num x0) = (int_of_num (NUMERAL 0))).
Definition term23 (x0 : int -> Prop) := forall y0 : int, x0 y0.
Definition term29 (x0 : real) (x1 : int) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (int_of_num (NUMERAL 0)))).
Definition term27 (x0 : real) := fun y0 : int => ((real_zpow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (int_of_num (NUMERAL 0))))).
Definition term5 (x0 : real) (x1 : nat) := (fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term71 := forall y0 : nat, True.
Definition term40 (x0 : real) := and (forall y0 : nat, (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) (int_of_num y0)).
Definition term42 (x0 : real) (x1 : nat) := (fun y0 : int => ((real_zpow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (int_of_num (NUMERAL 0)))))) (int_neg (int_of_num x1)).
Definition term70 := fun y0 : nat => True.
Definition term58 (x0 : real) (x1 : nat) := @eq Prop ((real_zpow x0 (int_neg (int_of_num x1))) = (real_of_num (NUMERAL 0))).
Definition term62 := fun y0 : real => forall y1 : int, ((real_zpow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0))))).
Definition term15 (x0 : real) (x1 : nat) := real_zpow x0 (int_neg (int_of_num x1)).
Definition term66 (x0 : real) (x1 : nat) := @eq Prop ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0)))).
Definition term32 (x0 : real) := @eq Prop (forall y0 : int, (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) y0).
Definition term61 (x0 : real) := (forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0)))))) /\ (forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0)))))).
Definition term48 (x0 : real) := (forall y0 : nat, ((real_zpow x0 (int_of_num y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0)))))) /\ (forall y0 : nat, ((real_zpow x0 (int_neg (int_of_num y0))) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0)))))).
Definition term7 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ (x1 = (NUMERAL 0))).
Definition term20 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_zpow x0 (int_of_num y0)) = (real_pow x0 y0)) x1.
Definition term74 (x0 : nat) := int_neg (int_of_num x0).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1)) x0.
Definition term50 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term30 (x0 : real) := fun y0 : int => (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) y0.
Definition term38 (x0 : real) := forall y0 : nat, (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) (int_of_num y0).
Definition term59 (x0 : real) := fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))))).
Definition term53 (x0 : real) := fun y0 : nat => ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0))))).
Definition term65 := forall y0 : real, (forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y1) = (int_of_num (NUMERAL 0)))))) /\ (forall y1 : nat, ((real_pow y0 y1) = (real_of_num (NUMERAL 0))) = ((y0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y1)) = (int_of_num (NUMERAL 0)))))).
Definition term13 (x0 : real) := forall y0 : nat, (real_zpow x0 (int_neg (int_of_num y0))) = (real_inv (real_pow x0 y0)).
Definition term35 (x0 : real) (x1 : nat) := (x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num x1) = (int_of_num (NUMERAL 0)))).
Definition term16 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term75 (x0 : nat) := ~ ((int_neg (int_of_num x0)) = (int_of_num (NUMERAL 0))).
Definition term52 (x0 : real) (x1 : nat) := @eq Prop ((real_pow x0 x1) = (real_of_num (NUMERAL 0))).
Definition term21 (x0 : real) (x1 : nat) := real_zpow x0 (int_of_num x1).
Definition term45 (x0 : real) := fun y0 : nat => ((real_zpow x0 (int_neg (int_of_num y0))) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))))).
Definition term37 (x0 : real) := fun y0 : nat => ((real_zpow x0 (int_of_num y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0))))).
Definition term73 (x0 : Prop) := forall y0 : nat, x0.
Definition term69 (x0 : real) := and (x0 = (real_of_num (NUMERAL 0))).
Definition term46 (x0 : real) := forall y0 : nat, (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) (int_neg (int_of_num y0)).
Definition term10 (x0 : real) := (fun y0 : real => ((real_inv y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((int_of_num x0) = (int_of_num y0)) = (x0 = y0)) x1.
Definition term25 (x0 : real) := forall y0 : int, (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) y0.
Definition term34 (x0 : real) (x1 : nat) := (fun y0 : int => ((real_zpow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (int_of_num (NUMERAL 0)))))) (int_of_num x1).
Definition term57 (x0 : real) (x1 : nat) := @eq real (real_inv (real_pow x0 x1)).
Definition term44 (x0 : real) := fun y0 : nat => (fun y1 : int => ((real_zpow x0 y1) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y1 = (int_of_num (NUMERAL 0)))))) (int_neg (int_of_num y0)).
Definition term60 (x0 : real) := forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))))).
Definition term54 (x0 : real) := forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0))))).
Definition term47 (x0 : real) := forall y0 : nat, ((real_zpow x0 (int_neg (int_of_num y0))) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_neg (int_of_num y0)) = (int_of_num (NUMERAL 0))))).
Definition term39 (x0 : real) := forall y0 : nat, ((real_zpow x0 (int_of_num y0)) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ ((int_of_num y0) = (int_of_num (NUMERAL 0))))).
Definition term4 (x0 : real) := forall y0 : nat, ((real_pow x0 y0) = (real_of_num (NUMERAL 0))) = ((x0 = (real_of_num (NUMERAL 0))) /\ (~ (y0 = (NUMERAL 0)))).
