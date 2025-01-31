Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term53 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term16 (x0 : real) := forall y0 : real, (real_sub (real_sub x0 y0) x0) = (real_neg y0).
Definition term26 (x0 : real) (x1 : real) := real_sub (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) x1.
Definition term33 := real_of_num (NUMERAL 0).
Definition term25 (x0 : real) (x1 : real) := real_sub (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term88 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term82 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term4 (x0 : real) := fun y0 : real => (real_sub (real_sub x0 y0) x0) = (real_neg y0).
Definition term2 (x0 : real) := ~ (forall y0 : real, (real_sub (real_sub x0 y0) x0) = (real_neg y0)).
Definition term61 (x0 : real) (x1 : real) := real_neg (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1)).
Definition term62 := real_neg (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_sub (real_sub x0 y0) x0) = (real_neg y0)) x1).
Definition term43 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term10 (x0 : real) := fun y0 : real => ~ ((real_sub (real_sub x0 y0) x0) = (real_neg y0)).
Definition term80 (x0 : Prop) := exists y0 : real, x0.
Definition term95 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term64 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term104 := forall y0 : real, forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1).
Definition term47 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term78 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term20 := exists y0 : real, exists y1 : real, ~ ((real_sub (real_sub y0 y1) y0) = (real_neg y1)).
Definition term51 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term97 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term27 (x0 : real) (x1 : real) := real_add (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term13 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_sub (real_sub y1 y2) y1) = (real_neg y2)) y0).
Definition term3 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_sub (real_sub x0 y1) x0) = (real_neg y1)) y0).
Definition term18 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_sub (real_sub y1 y2) y1) = (real_neg y2)) y0).
Definition term32 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term54 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term74 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term21 (x0 : real) (x1 : real) := (real_gt (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term83 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term99 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term12 := ~ (forall y0 : real, forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1)).
Definition term70 (x0 : real) (x1 : real) := real_gt (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1)).
Definition term101 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term63 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term84 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term69 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term87 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term68 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1))) (real_of_num (NUMERAL 0)).
Definition term58 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term39 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub (real_sub x0 y0) x0) = (real_neg y0)) x1.
Definition term17 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1)) x0).
Definition term77 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term65 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1))).
Definition term60 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term6 (x0 : real) (x1 : real) := real_sub (real_sub x1 x0) x1.
Definition term56 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term93 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term92 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term42 (x0 : real) (x1 : real) := real_sub (real_sub (real_sub x1 x0) x1).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1)) x0.
Definition term100 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term30 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term31 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term72 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1)) (real_of_num (NUMERAL 0))).
Definition term102 := (~ (forall y0 : real, forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1))) -> False.
Definition term66 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1))).
Definition term37 := real_mul (real_of_num (NUMERAL 0)).
Definition term71 (x0 : real) (x1 : real) := real_gt (real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1)) (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term22 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term79 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term19 := fun y0 : real => exists y1 : real, ~ ((real_sub (real_sub y0 y1) y0) = (real_neg y1)).
Definition term57 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term91 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term11 (x0 : real) := exists y0 : real, ~ ((real_sub (real_sub x0 y0) x0) = (real_neg y0)).
Definition term85 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term75 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term103 := ((~ (forall y0 : real, forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1))) -> False) -> forall y0 : real, forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1).
Definition term41 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term90 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term49 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term52 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term55 := real_of_num (NUMERAL (BIT1 0)).
Definition term59 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term44 (x0 : real) (x1 : real) := real_sub (real_sub (real_sub x0 x1) x0) (real_neg x1).
Definition term94 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term38 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term48 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term8 (x0 : real) (x1 : real) := ~ ((real_sub (real_sub x0 x1) x0) = (real_neg x1)).
Definition term9 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_sub (real_sub x0 y1) x0) = (real_neg y1)) y0).
Definition term73 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term50 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term89 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term14 := fun y0 : real => forall y1 : real, (real_sub (real_sub y0 y1) y0) = (real_neg y1).
Definition term24 (x0 : real) (x1 : real) := real_sub (real_sub x0 x1).
Definition term45 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term23 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term34 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term46 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term40 := real_add (real_of_num (NUMERAL 0)).
Definition term98 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term35 := NUMERAL (BIT1 0).
Definition term86 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term76 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term29 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term96 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term67 := real_gt (real_of_num (NUMERAL 0)).
