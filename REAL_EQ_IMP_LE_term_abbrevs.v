Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term83 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term2 (x0 : real -> Prop) := ~ (all x0).
Definition term64 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term22 := real_of_num (NUMERAL 0).
Definition term24 (x0 : real) (x1 : real) := @eq real (real_sub x0 x1).
Definition term53 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul y0 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term4 (x0 : real) := ~ (forall y0 : real, (x0 = y0) -> real_le x0 y0).
Definition term34 (x0 : real) := fun y0 : real => ((real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term6 (x0 : real) := fun y0 : real => (x0 = y0) -> real_le x0 y0.
Definition term9 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (x0 = y0) -> real_le x0 y0) x1).
Definition term1 (x0 : real) (x1 : real) := (x0 = x1) /\ (~ (real_le x0 x1)).
Definition term70 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term47 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term40 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term96 := forall y0 : real, forall y1 : real, (y0 = y1) -> real_le y0 y1.
Definition term58 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term86 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term37 := exists y0 : real, exists y1 : real, ((real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term21 := exists y0 : real, exists y1 : real, (y0 = y1) /\ (~ (real_le y0 y1)).
Definition term62 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term48 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term76 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term14 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (y1 = y2) -> real_le y1 y2) y0).
Definition term5 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (x0 = y1) -> real_le x0 y1) y0).
Definition term29 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term32 (x0 : real) (x1 : real) := and ((real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) = (real_of_num (NUMERAL 0))).
Definition term19 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (y1 = y2) -> real_le y1 y2) y0).
Definition term20 := fun y0 : real => exists y1 : real, (y0 = y1) /\ (~ (real_le y0 y1)).
Definition term11 (x0 : real) := fun y0 : real => (x0 = y0) /\ (~ (real_le x0 y0)).
Definition term81 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term65 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term13 := ~ (forall y0 : real, forall y1 : real, (y0 = y1) -> real_le y0 y1).
Definition term93 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term51 (x0 : real) (x1 : real) := ((real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) = (real_of_num (NUMERAL 0)).
Definition term92 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term68 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term18 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (y0 = y1) -> real_le y0 y1) x0).
Definition term36 := fun y0 : real => exists y1 : real, ((real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term33 (x0 : real) (x1 : real) := ((real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term79 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term66 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term8 (x0 : real) (x1 : real) := (x0 = x1) -> real_le x0 x1.
Definition term43 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term15 := fun y0 : real => forall y1 : real, (y0 = y1) -> real_le y0 y1.
Definition term3 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) -> real_le y0 y1) x0.
Definition term38 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term42 := S (Nat.add 0 0).
Definition term71 (x0 : real) (x1 : real) := @eq real (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term17 (x0 : real) := forall y0 : real, (x0 = y0) -> real_le x0 y0.
Definition term80 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term25 (x0 : real) (x1 : real) := @eq real (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term54 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term94 := (~ (forall y0 : real, forall y1 : real, (y0 = y1) -> real_le y0 y1)) -> False.
Definition term78 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term7 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) -> real_le x0 y0) x1.
Definition term84 := real_mul (real_of_num (NUMERAL 0)).
Definition term57 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term67 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term95 := ((~ (forall y0 : real, forall y1 : real, (y0 = y1) -> real_le y0 y1)) -> False) -> forall y0 : real, forall y1 : real, (y0 = y1) -> real_le y0 y1.
Definition term0 (x0 : real) (x1 : real) := ~ ((x0 = x1) -> real_le x0 x1).
Definition term27 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term60 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term26 (x0 : real) (x1 : real) := ~ (real_le x0 x1).
Definition term12 (x0 : real) := exists y0 : real, (x0 = y0) /\ (~ (real_le x0 y0)).
Definition term63 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term46 := real_of_num (NUMERAL (BIT1 0)).
Definition term69 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term35 (x0 : real) := exists y0 : real, ((real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term31 (x0 : real) (x1 : real) := and (x0 = x1).
Definition term85 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term59 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term52 (x0 : real) (x1 : real) := forall y0 : real, (real_mul y0 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) = (real_of_num (NUMERAL 0)).
Definition term10 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (x0 = y1) -> real_le x0 y1) y0).
Definition term73 (x0 : real) (x1 : real) := ((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term61 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term89 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term50 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term90 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term55 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term23 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term82 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term75 (x0 : real) (x1 : real) := (((real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term72 (x0 : real) (x1 : real) := @eq real (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term28 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term87 := real_add (real_of_num (NUMERAL 0)).
Definition term77 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term56 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term41 := NUMERAL (BIT1 0).
Definition term74 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term44 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term88 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term39 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term91 := real_gt (real_of_num (NUMERAL 0)).
