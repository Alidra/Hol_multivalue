Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : int) (x1 : int) := (fun y0 : int => forall y1 : int, (int_add x0 (int_add y0 y1)) = (int_add (int_add x0 y0) y1)) x1.
Definition term51 (x0 : nat) (x1 : nat) := @eq int (int_add (int_add (int_neg (int_of_num x1)) (int_neg (int_of_num x0))) (int_of_num x1)).
Definition term54 (x0 : nat) (x1 : nat) := and ((int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) (int_of_num x0)) = (int_neg (int_of_num x1))).
Definition term53 (x0 : nat) (x1 : nat) := and ((int_add (int_neg (int_of_num (Nat.add x0 x1))) (int_of_num x0)) = (int_neg (int_of_num x1))).
Definition term91 (x0 : nat) (x1 : nat) := True /\ (((int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ ((int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))) (int_neg (int_of_num x1))) = (int_neg (int_of_num x1))))).
Definition term35 (x0 : nat) (x1 : nat) := int_neg (int_add (int_of_num x0) (int_of_num x1)).
Definition term4 := int_of_num (NUMERAL 0).
Definition term27 (x0 : int) := (fun y0 : int => forall y1 : int, (int_neg (int_add y0 y1)) = (int_add (int_neg y0) (int_neg y1))) x0.
Definition term14 (x0 : int) := (fun y0 : int => forall y1 : int, (int_add y0 y1) = (int_add y1 y0)) x0.
Definition term74 (x0 : nat) (x1 : nat) := ((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ ((int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))) = (int_neg (int_of_num x1))).
Definition term7 (x0 : int) := (fun y0 : int => forall y1 : int, forall y2 : int, (int_add y0 (int_add y1 y2)) = (int_add (int_add y0 y1) y2)) x0.
Definition term11 (x0 : int) (x1 : int) (x2 : int) := (fun y0 : int => (int_add x0 (int_add x1 y0)) = (int_add (int_add x0 x1) y0)) x2.
Definition term5 (x0 : int) := (fun y0 : int => (int_add (int_neg y0) y0) = (int_of_num (NUMERAL 0))) x0.
Definition term75 (x0 : nat) (x1 : nat) := ((int_add (int_neg (int_of_num (Nat.add x0 x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_of_num (Nat.add x0 x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ (((int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1)))) = (int_neg (int_of_num x1))) /\ ((int_add (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.add x0 x1))))).
Definition term87 (x0 : nat) (x1 : nat) := int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))) (int_neg (int_of_num x1)).
Definition term55 (x0 : nat) (x1 : nat) := int_add (int_of_num (Nat.add x0 x1)).
Definition term0 (x0 : int) := (fun y0 : int => (int_add (int_of_num (NUMERAL 0)) y0) = y0) x0.
Definition term40 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num x0)) (int_of_num (Nat.add x0 x1)).
Definition term30 (x0 : int) (x1 : int) := int_neg (int_add x0 x1).
Definition term28 (x0 : int) := forall y0 : int, (int_neg (int_add x0 y0)) = (int_add (int_neg x0) (int_neg y0)).
Definition term100 (x0 : nat) (x1 : nat) := ((int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))) (int_neg (int_of_num x1))) = (int_neg (int_of_num x1))) /\ True.
Definition term72 (x0 : nat) (x1 : nat) := ((int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))) = (int_neg (int_of_num x1))) /\ True.
Definition term1 (x0 : int) := int_add (int_of_num (NUMERAL 0)) x0.
Definition term79 (x0 : nat) (x1 : nat) := ((int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (int_neg (int_of_num (Nat.add x0 x1)))) /\ (((int_add (int_neg (int_of_num x0)) (int_of_num (Nat.add x0 x1))) = (int_of_num x1)) /\ (((int_add (int_neg (int_of_num (Nat.add x0 x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_of_num (Nat.add x0 x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ (((int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1)))) = (int_neg (int_of_num x1))) /\ ((int_add (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.add x0 x1))))))).
Definition term69 (x0 : nat) (x1 : nat) := and ((int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))) = (int_neg (int_of_num x1))).
Definition term16 (x0 : int) (x1 : int) := (fun y0 : int => (int_add x0 y0) = (int_add y0 x0)) x1.
Definition term48 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num (Nat.add x1 x0))) (int_of_num x1).
Definition term84 := int_add (int_of_num (NUMERAL 0)).
Definition term10 (x0 : int) (x1 : int) := forall y0 : int, (int_add x0 (int_add x1 y0)) = (int_add (int_add x0 x1) y0).
Definition term80 (x0 : nat) (x1 : nat) := True /\ (((int_add (int_neg (int_of_num x0)) (int_add (int_of_num x0) (int_of_num x1))) = (int_of_num x1)) /\ (((int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ ((int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))) = (int_neg (int_of_num x1)))))).
Definition term15 (x0 : int) := forall y0 : int, (int_add x0 y0) = (int_add y0 x0).
Definition term26 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1)).
Definition term25 := forall y0 : nat, forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1)).
Definition term67 (x0 : nat) (x1 : nat) := @eq int (int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))).
Definition term97 (x0 : nat) (x1 : nat) := ((int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ ((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)).
Definition term13 (x0 : int) (x1 : int) (x2 : int) := int_add (int_add x0 x1) x2.
Definition term22 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0)).
Definition term57 (x0 : nat) (x1 : nat) := int_add (int_of_num (Nat.add x1 x0)) (int_neg (int_of_num x1)).
Definition term83 (x0 : nat) := int_add (int_add (int_neg (int_of_num x0)) (int_of_num x0)).
Definition term89 (x0 : nat) (x1 : nat) := ((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ ((int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))) (int_neg (int_of_num x1))) = (int_neg (int_of_num x1))).
Definition term59 (x0 : nat) (x1 : nat) := @eq int (int_add (int_of_num (Nat.add x1 x0)) (int_neg (int_of_num x1))).
Definition term8 (x0 : int) := forall y0 : int, forall y1 : int, (int_add x0 (int_add y0 y1)) = (int_add (int_add x0 y0) y1).
Definition term37 (x0 : nat) (x1 : nat) := @eq int (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))).
Definition term63 (x0 : nat) := int_add (int_of_num x0).
Definition term78 (x0 : nat) (x1 : nat) := ((int_add (int_neg (int_of_num x0)) (int_add (int_of_num x0) (int_of_num x1))) = (int_of_num x1)) /\ (((int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ ((int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))) = (int_neg (int_of_num x1))))).
Definition term81 (x0 : nat) (x1 : nat) := int_add (int_add (int_neg (int_of_num x0)) (int_of_num x0)) (int_of_num x1).
Definition term64 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1))).
Definition term43 (x0 : nat) (x1 : nat) := @eq int (int_add (int_neg (int_of_num x0)) (int_add (int_of_num x0) (int_of_num x1))).
Definition term21 (x0 : nat) := forall y0 : nat, (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0)).
Definition term38 (x0 : nat) (x1 : nat) := and ((int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) = (int_neg (int_of_num (Nat.add x0 x1)))).
Definition term98 (x0 : nat) (x1 : nat) := ((int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))) = (int_neg (int_of_num x1))) /\ ((int_add (int_neg (int_of_num x0)) (int_add (int_of_num x0) (int_of_num x1))) = (int_of_num x1)).
Definition term71 (x0 : nat) (x1 : nat) := ((int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1)))) = (int_neg (int_of_num x1))) /\ ((int_add (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.add x0 x1))).
Definition term42 (x0 : nat) (x1 : nat) := @eq int (int_add (int_neg (int_of_num x0)) (int_of_num (Nat.add x0 x1))).
Definition term34 (x0 : nat) (x1 : nat) := int_neg (int_of_num (Nat.add x0 x1)).
Definition term86 (x0 : nat) := @eq int (int_of_num x0).
Definition term82 (x0 : nat) := int_add (int_neg (int_of_num x0)) (int_of_num x0).
Definition term33 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0))) x1.
Definition term62 (x0 : nat) (x1 : nat) := and ((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)).
Definition term61 (x0 : nat) (x1 : nat) := and ((int_add (int_of_num (Nat.add x0 x1)) (int_neg (int_of_num x0))) = (int_of_num x1)).
Definition term44 (x0 : nat) (x1 : nat) := and ((int_add (int_neg (int_of_num x0)) (int_of_num (Nat.add x0 x1))) = (int_of_num x1)).
Definition term60 (x0 : nat) (x1 : nat) := @eq int (int_add (int_add (int_of_num x1) (int_of_num x0)) (int_neg (int_of_num x1))).
Definition term2 (x0 : int) := (fun y0 : int => (int_add y0 (int_neg y0)) = (int_of_num (NUMERAL 0))) x0.
Definition term49 (x0 : nat) (x1 : nat) := int_add (int_add (int_neg (int_of_num x1)) (int_neg (int_of_num x0))) (int_of_num x1).
Definition term6 (x0 : int) := int_add (int_neg x0) x0.
Definition term52 (x0 : nat) := int_neg (int_of_num x0).
Definition term85 (x0 : nat) := int_add (int_of_num (NUMERAL 0)) (int_of_num x0).
Definition term65 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))).
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1))) x0.
Definition term56 (x0 : nat) (x1 : nat) := int_add (int_add (int_of_num x0) (int_of_num x1)).
Definition term31 (x0 : int) (x1 : int) := int_add (int_neg x0) (int_neg x1).
Definition term70 (x0 : nat) (x1 : nat) := @eq int (int_add (int_of_num x0) (int_of_num x1)).
Definition term19 (x0 : nat) := fun y0 : nat => (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0)).
Definition term94 (x0 : nat) := int_add (int_of_num (NUMERAL 0)) (int_neg (int_of_num x0)).
Definition term77 (x0 : nat) (x1 : nat) := ((int_add (int_neg (int_of_num x0)) (int_of_num (Nat.add x0 x1))) = (int_of_num x1)) /\ (((int_add (int_neg (int_of_num (Nat.add x0 x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_of_num (Nat.add x0 x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ (((int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1)))) = (int_neg (int_of_num x1))) /\ ((int_add (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.add x0 x1)))))).
Definition term66 (x0 : nat) (x1 : nat) := @eq int (int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1)))).
Definition term92 (x0 : nat) := int_add (int_of_num x0) (int_neg (int_of_num x0)).
Definition term20 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0)).
Definition term58 (x0 : nat) (x1 : nat) := int_add (int_add (int_of_num x1) (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term47 (x0 : nat) (x1 : nat) := int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))).
Definition term23 := fun y0 : nat => forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1)).
Definition term39 (x0 : nat) := int_add (int_neg (int_of_num x0)).
Definition term36 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)).
Definition term12 (x0 : int) (x1 : int) (x2 : int) := int_add x0 (int_add x1 x2).
Definition term18 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term45 (x0 : nat) (x1 : nat) := and ((int_add (int_neg (int_of_num x0)) (int_add (int_of_num x0) (int_of_num x1))) = (int_of_num x1)).
Definition term90 (x0 : nat) (x1 : nat) := ((int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ ((int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))) (int_neg (int_of_num x1))) = (int_neg (int_of_num x1)))).
Definition term76 (x0 : nat) (x1 : nat) := ((int_add (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1))) (int_of_num x0)) = (int_neg (int_of_num x1))) /\ (((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ ((int_add (int_of_num x0) (int_add (int_neg (int_of_num x0)) (int_neg (int_of_num x1)))) = (int_neg (int_of_num x1)))).
Definition term95 (x0 : nat) := @eq int (int_neg (int_of_num x0)).
Definition term41 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num x0)) (int_add (int_of_num x0) (int_of_num x1)).
Definition term96 (x0 : nat) (x1 : nat) := ((int_add (int_add (int_of_num x0) (int_of_num x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ True.
Definition term99 (x0 : nat) (x1 : nat) := and ((int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))) (int_neg (int_of_num x1))) = (int_neg (int_of_num x1))).
Definition term68 (x0 : nat) (x1 : nat) := and ((int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1)))) = (int_neg (int_of_num x1))).
Definition term93 (x0 : nat) := int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))).
Definition term17 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term50 (x0 : nat) (x1 : nat) := @eq int (int_add (int_neg (int_of_num (Nat.add x1 x0))) (int_of_num x1)).
Definition term46 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num (Nat.add x0 x1))).
Definition term24 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1)).
Definition term3 (x0 : int) := int_add x0 (int_neg x0).
Definition term73 (x0 : nat) (x1 : nat) := ((int_add (int_of_num (Nat.add x0 x1)) (int_neg (int_of_num x0))) = (int_of_num x1)) /\ (((int_add (int_of_num x0) (int_neg (int_of_num (Nat.add x0 x1)))) = (int_neg (int_of_num x1))) /\ ((int_add (int_of_num x0) (int_of_num x1)) = (int_of_num (Nat.add x0 x1)))).
Definition term88 (x0 : nat) (x1 : nat) := @eq int (int_add (int_add (int_of_num x0) (int_neg (int_of_num x0))) (int_neg (int_of_num x1))).
Definition term29 (x0 : int) (x1 : int) := (fun y0 : int => (int_neg (int_add x0 y0)) = (int_add (int_neg x0) (int_neg y0))) x1.
