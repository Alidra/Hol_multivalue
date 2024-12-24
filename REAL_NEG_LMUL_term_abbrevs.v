Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term53 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term67 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1)) (real_of_num (NUMERAL 0))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term41 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term34 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term51 := real_of_num (NUMERAL 0).
Definition term30 (x0 : real) (x1 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term29 (x0 : real) (x1 : real) := real_sub (real_neg (real_mul x0 x1)).
Definition term83 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term12 (x0 : real) := exists y0 : real, ~ ((real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0)).
Definition term24 (x0 : real) := real_mul (real_neg x0).
Definition term77 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term26 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term2 (x0 : real) := ~ (forall y0 : real, (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0)).
Definition term57 := real_neg (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term8 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0)) x1).
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0)) x1.
Definition term66 (x0 : real) (x1 : real) := real_gt (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1)) (real_of_num (NUMERAL 0)).
Definition term75 (x0 : Prop) := exists y0 : real, x0.
Definition term90 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term59 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term99 := forall y0 : real, forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1).
Definition term11 (x0 : real) := fun y0 : real => ~ ((real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0)).
Definition term73 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term21 := exists y0 : real, exists y1 : real, ~ ((real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1)).
Definition term38 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term92 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term32 (x0 : real) (x1 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term6 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term14 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_neg (real_mul y1 y2)) = (real_mul (real_neg y1) y2)) y0).
Definition term3 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_neg (real_mul x0 y1)) = (real_mul (real_neg x0) y1)) y0).
Definition term19 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_neg (real_mul y1 y2)) = (real_mul (real_neg y1) y2)) y0).
Definition term60 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1))).
Definition term50 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term42 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term69 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term22 (x0 : real) (x1 : real) := (real_gt (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1))) (real_of_num (NUMERAL 0))).
Definition term78 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term94 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term13 := ~ (forall y0 : real, forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1)).
Definition term96 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term58 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term79 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term63 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1))) (real_of_num (NUMERAL 0)).
Definition term64 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term82 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term18 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1)) x0).
Definition term72 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term47 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term44 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term88 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term87 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term15 := fun y0 : real => forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1)) x0.
Definition term95 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term25 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term33 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))).
Definition term7 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term28 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term97 := (~ (forall y0 : real, forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1))) -> False.
Definition term54 := real_mul (real_of_num (NUMERAL 0)).
Definition term23 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term74 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term20 := fun y0 : real => exists y1 : real, ~ ((real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1)).
Definition term45 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term86 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term27 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term80 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term70 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term98 := ((~ (forall y0 : real, forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1))) -> False) -> forall y0 : real, forall y1 : real, (real_neg (real_mul y0 y1)) = (real_mul (real_neg y0) y1).
Definition term85 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term36 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term39 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term43 := real_of_num (NUMERAL (BIT1 0)).
Definition term46 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1).
Definition term89 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term48 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul x0 x1).
Definition term4 (x0 : real) := fun y0 : real => (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0).
Definition term35 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul x0 x1).
Definition term65 (x0 : real) (x1 : real) := real_gt (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1)).
Definition term10 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_neg (real_mul x0 y1)) = (real_mul (real_neg x0) y1)) y0).
Definition term61 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1))).
Definition term9 (x0 : real) (x1 : real) := ~ ((real_neg (real_mul x0 x1)) = (real_mul (real_neg x0) x1)).
Definition term68 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term37 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term84 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term52 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term56 (x0 : real) (x1 : real) := real_neg (real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1)).
Definition term17 (x0 : real) := forall y0 : real, (real_neg (real_mul x0 y0)) = (real_mul (real_neg x0) y0).
Definition term93 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term76 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term40 := NUMERAL (BIT1 0).
Definition term81 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term71 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term31 (x0 : real) (x1 : real) := real_sub (real_neg (real_mul x0 x1)) (real_mul (real_neg x0) x1).
Definition term91 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term62 := real_gt (real_of_num (NUMERAL 0)).
