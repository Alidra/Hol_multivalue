Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term11 := exists y0 : real, ~ ((real_sub y0 y0) = (real_of_num (NUMERAL 0))).
Definition term6 := real_of_num (NUMERAL 0).
Definition term24 (x0 : real) := real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0)).
Definition term52 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term46 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term70 := forall y0 : real, (real_sub y0 y0) = (real_of_num (NUMERAL 0)).
Definition term39 (x0 : real) := real_gt (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term2 := ~ (forall y0 : real, (real_sub y0 y0) = (real_of_num (NUMERAL 0))).
Definition term32 := real_neg (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) := @eq real (real_neg (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0)))).
Definition term26 := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term69 := ((~ (forall y0 : real, (real_sub y0 y0) = (real_of_num (NUMERAL 0)))) -> False) -> forall y0 : real, (real_sub y0 y0) = (real_of_num (NUMERAL 0)).
Definition term10 := fun y0 : real => ~ ((real_sub y0 y0) = (real_of_num (NUMERAL 0))).
Definition term65 (x0 : Prop) := exists y0 : real, x0.
Definition term59 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term27 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term61 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term22 (x0 : real) := real_sub (real_sub x0 x0).
Definition term3 := exists y0 : real, ~ ((fun y1 : real => (real_sub y1 y1) = (real_of_num (NUMERAL 0))) y0).
Definition term16 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term42 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term12 (x0 : real) := (real_gt (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term47 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term63 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term67 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term28 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term23 := real_sub (real_of_num (NUMERAL 0)).
Definition term48 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term37 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term51 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term8 (x0 : real) := ~ ((real_sub x0 x0) = (real_of_num (NUMERAL 0))).
Definition term38 (x0 : real) := real_gt (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0))).
Definition term57 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term56 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term36 (x0 : real) := real_gt (real_neg (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term4 := fun y0 : real => (real_sub y0 y0) = (real_of_num (NUMERAL 0)).
Definition term14 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term15 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term68 := (~ (forall y0 : real, (real_sub y0 y0) = (real_of_num (NUMERAL 0)))) -> False.
Definition term20 := real_mul (real_of_num (NUMERAL 0)).
Definition term64 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term55 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term49 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term43 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term34 (x0 : real) := real_gt (real_neg (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0)))).
Definition term54 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term40 (x0 : real) := or (real_gt (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term58 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term21 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term7 (x0 : real) := ~ ((fun y0 : real => (real_sub y0 y0) = (real_of_num (NUMERAL 0))) x0).
Definition term9 := fun y0 : real => ~ ((fun y1 : real => (real_sub y1 y1) = (real_of_num (NUMERAL 0))) y0).
Definition term41 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term53 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term30 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term17 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term5 (x0 : real) := (fun y0 : real => (real_sub y0 y0) = (real_of_num (NUMERAL 0))) x0.
Definition term29 := real_add (real_of_num (NUMERAL 0)).
Definition term62 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term45 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term18 := NUMERAL (BIT1 0).
Definition term50 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term25 := real_sub (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term44 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term13 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term60 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term31 (x0 : real) := real_neg (real_sub (real_sub x0 x0) (real_of_num (NUMERAL 0))).
Definition term35 := real_gt (real_of_num (NUMERAL 0)).
