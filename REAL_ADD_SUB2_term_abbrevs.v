Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : real) (x1 : real) := ~ ((real_sub x0 (real_add x0 x1)) = (real_neg x1)).
Definition term35 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term52 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term32 := real_of_num (NUMERAL 0).
Definition term24 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term10 (x0 : real) := fun y0 : real => ~ ((real_sub x0 (real_add x0 y0)) = (real_neg y0)).
Definition term87 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term81 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term2 (x0 : real) := ~ (forall y0 : real, (real_sub x0 (real_add x0 y0)) = (real_neg y0)).
Definition term61 := real_neg (real_of_num (NUMERAL 0)).
Definition term7 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_sub x0 (real_add x0 y0)) = (real_neg y0)) x1).
Definition term42 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term4 (x0 : real) := fun y0 : real => (real_sub x0 (real_add x0 y0)) = (real_neg y0).
Definition term79 (x0 : Prop) := exists y0 : real, x0.
Definition term94 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term63 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term103 := forall y0 : real, forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1).
Definition term46 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term77 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term20 := exists y0 : real, exists y1 : real, ~ ((real_sub y0 (real_add y0 y1)) = (real_neg y1)).
Definition term50 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term96 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term60 (x0 : real) (x1 : real) := real_neg (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1)).
Definition term13 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_sub y1 (real_add y1 y2)) = (real_neg y2)) y0).
Definition term3 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_sub x0 (real_add x0 y1)) = (real_neg y1)) y0).
Definition term65 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1))).
Definition term18 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_sub y1 (real_add y1 y2)) = (real_neg y2)) y0).
Definition term31 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term53 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term73 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term23 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1)).
Definition term21 (x0 : real) (x1 : real) := (real_gt (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1))) (real_of_num (NUMERAL 0))).
Definition term82 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term98 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term12 := ~ (forall y0 : real, forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1)).
Definition term100 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term62 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term64 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1))).
Definition term6 (x0 : real) (x1 : real) := real_sub x0 (real_add x0 x1).
Definition term25 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term83 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term68 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term16 (x0 : real) := forall y0 : real, (real_sub x0 (real_add x0 y0)) = (real_neg y0).
Definition term86 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term67 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1))) (real_of_num (NUMERAL 0)).
Definition term57 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term38 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term17 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1)) x0).
Definition term76 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term59 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term55 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term92 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term91 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term15 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1)) x0.
Definition term99 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term30 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term26 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term71 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1)) (real_of_num (NUMERAL 0))).
Definition term101 := (~ (forall y0 : real, forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1))) -> False.
Definition term36 := real_mul (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term22 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term78 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term19 := fun y0 : real => exists y1 : real, ~ ((real_sub y0 (real_add y0 y1)) = (real_neg y1)).
Definition term56 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term90 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_sub x0 (real_add x0 y0)) = (real_neg y0)) x1.
Definition term11 (x0 : real) := exists y0 : real, ~ ((real_sub x0 (real_add x0 y0)) = (real_neg y0)).
Definition term84 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term74 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term102 := ((~ (forall y0 : real, forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1))) -> False) -> forall y0 : real, forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1).
Definition term41 (x0 : real) (x1 : real) := real_sub (real_sub x0 (real_add x0 x1)).
Definition term40 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term89 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term48 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term51 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term54 := real_of_num (NUMERAL (BIT1 0)).
Definition term58 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term70 (x0 : real) (x1 : real) := real_gt (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1)) (real_of_num (NUMERAL 0)).
Definition term93 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term37 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term69 (x0 : real) (x1 : real) := real_gt (real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1)).
Definition term47 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term9 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_sub x0 (real_add x0 y1)) = (real_neg y1)) y0).
Definition term43 (x0 : real) (x1 : real) := real_sub (real_sub x0 (real_add x0 x1)) (real_neg x1).
Definition term72 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term49 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term88 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term27 (x0 : real) (x1 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term14 := fun y0 : real => forall y1 : real, (real_sub y0 (real_add y0 y1)) = (real_neg y1).
Definition term44 (x0 : real) := real_sub (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term33 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term45 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term39 := real_add (real_of_num (NUMERAL 0)).
Definition term97 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term80 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term34 := NUMERAL (BIT1 0).
Definition term85 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term75 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term29 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term95 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term66 := real_gt (real_of_num (NUMERAL 0)).
