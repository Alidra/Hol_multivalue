Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term57 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term8 (x0 : real -> Prop) := ~ (all x0).
Definition term51 (x0 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term39 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term1 := real_of_num (NUMERAL 0).
Definition term45 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term12 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term3 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (~ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term10 := ~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0)))).
Definition term32 := exists y0 : real, (real_gt y0 (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term28 (x0 : real) := @eq real (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term46 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term26 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term19 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term35 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term65 := ((~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0))))) -> False) -> forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0))).
Definition term22 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term18 := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term20 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term2 (x0 : real) := and (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term14 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) -> ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term7 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term11 := exists y0 : real, ~ ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) y1) -> ~ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term21 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term13 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term55 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term63 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term23 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term27 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term62 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term42 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term66 := forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0))).
Definition term53 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term29 (x0 : real) := and (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term31 := fun y0 : real => (real_gt y0 (real_of_num (NUMERAL 0))) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term9 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term33 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term36 := S (Nat.add 0 0).
Definition term54 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term17 := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) /\ (y0 = (real_of_num (NUMERAL 0))).
Definition term47 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term64 := (~ (forall y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0))))) -> False.
Definition term5 (x0 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) -> ~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term58 := real_mul (real_of_num (NUMERAL 0)).
Definition term43 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term48 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term6 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term49 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term4 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term40 := real_of_num (NUMERAL (BIT1 0)).
Definition term59 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term60 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term52 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term15 (x0 : real) := ~ ((fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) -> ~ (y0 = (real_of_num (NUMERAL 0)))) x0).
Definition term16 := fun y0 : real => ~ ((fun y1 : real => (real_lt (real_of_num (NUMERAL 0)) y1) -> ~ (y1 = (real_of_num (NUMERAL 0)))) y0).
Definition term44 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term41 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term56 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term0 (x0 : real) := ~ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term37 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term24 := NUMERAL (BIT1 0).
Definition term50 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term34 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term61 := real_gt (real_of_num (NUMERAL 0)).
