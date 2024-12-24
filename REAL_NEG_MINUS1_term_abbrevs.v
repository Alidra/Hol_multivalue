Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term38 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term52 (x0 : real) := or (real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term26 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term46 (x0 : real) := real_gt (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))).
Definition term36 := real_of_num (NUMERAL 0).
Definition term64 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term11 := exists y0 : real, ~ ((real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)).
Definition term50 (x0 : real) := real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term58 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term2 := ~ (forall y0 : real, (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)).
Definition term13 (x0 : real) := real_sub (real_neg x0).
Definition term42 := real_neg (real_of_num (NUMERAL 0)).
Definition term51 (x0 : real) := real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term4 := fun y0 : real => (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term14 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term41 (x0 : real) := real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term81 := ((~ (forall y0 : real, (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0))) -> False) -> forall y0 : real, (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term77 (x0 : Prop) := exists y0 : real, x0.
Definition term71 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term44 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term18 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term23 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term73 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term3 := exists y0 : real, ~ ((fun y1 : real => (real_neg y1) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) y0).
Definition term35 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term27 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term54 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term12 (x0 : real) := (real_gt (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))) (real_of_num (NUMERAL 0))).
Definition term59 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term75 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term79 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term43 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term60 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term48 (x0 : real) := real_gt (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))) (real_of_num (NUMERAL 0)).
Definition term49 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term63 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term31 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term33 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term29 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term15 (x0 : real) := real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term69 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term68 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term78 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term34 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term20 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term82 := forall y0 : real, (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0).
Definition term80 := (~ (forall y0 : real, (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0))) -> False.
Definition term39 := real_mul (real_of_num (NUMERAL 0)).
Definition term6 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term76 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term30 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term67 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term61 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term55 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term8 (x0 : real) := ~ ((real_neg x0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term66 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term21 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term10 := fun y0 : real => ~ ((real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)).
Definition term24 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term5 (x0 : real) := (fun y0 : real => (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) x0.
Definition term28 := real_of_num (NUMERAL (BIT1 0)).
Definition term32 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term70 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term40 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term19 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term7 (x0 : real) := ~ ((fun y0 : real => (real_neg y0) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) x0).
Definition term9 := fun y0 : real => ~ ((fun y1 : real => (real_neg y1) = (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) y0).
Definition term53 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term22 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term65 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term45 (x0 : real) := @eq real (real_neg (real_sub (real_neg x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0))).
Definition term16 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term37 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term17 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term74 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term57 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term25 := NUMERAL (BIT1 0).
Definition term62 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term56 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term72 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term47 := real_gt (real_of_num (NUMERAL 0)).
