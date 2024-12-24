Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2.
Definition term44 (x0 : real) (x1 : real) := real_add (real_mul x0 x1).
Definition term75 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term59 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term93 (x0 : real) (x1 : real) (x2 : real) := or (real_gt (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2))) (real_of_num (NUMERAL 0))).
Definition term52 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term73 := real_of_num (NUMERAL 0).
Definition term111 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term40 (x0 : real) (x1 : real) := real_mul x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term49 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2)))).
Definition term105 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term2 (x0 : real) (x1 : real) := ~ (forall y0 : real, (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0))).
Definition term83 := real_neg (real_of_num (NUMERAL 0)).
Definition term71 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term6 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_sub x0 x1) x2.
Definition term91 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2))).
Definition term11 (x0 : real) (x1 : real) := fun y0 : real => ~ ((real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0))).
Definition term35 (x0 : real) (x1 : real) := real_mul (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term78 (x0 : real) (x1 : real) := real_add (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))).
Definition term103 (x0 : Prop) := exists y0 : real, x0.
Definition term118 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term85 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term127 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2)).
Definition term26 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1)).
Definition term101 := exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term99 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term30 := exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2))).
Definition term21 (x0 : real) := exists y0 : real, exists y1 : real, ~ ((real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1))).
Definition term56 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term120 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term7 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul x0 x2) (real_mul x1 x2).
Definition term92 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2))) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul x1 x0) (real_mul x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term70 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term23 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_mul (real_sub y1 y2) y3) = (real_sub (real_mul y1 y3) (real_mul y2 y3))) y0).
Definition term14 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul (real_sub x0 y1) y2) = (real_sub (real_mul x0 y2) (real_mul y1 y2))) y0).
Definition term3 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_sub (real_mul x0 y1) (real_mul x1 y1))) y0).
Definition term28 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_mul (real_sub y1 y2) y3) = (real_sub (real_mul y1 y3) (real_mul y2 y3))) y0).
Definition term19 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul (real_sub x0 y1) y2) = (real_sub (real_mul x0 y2) (real_mul y1 y2))) y0).
Definition term15 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1)).
Definition term46 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))).
Definition term72 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term60 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term95 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term31 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2)))) (real_of_num (NUMERAL 0))).
Definition term106 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term122 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term22 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2))).
Definition term13 (x0 : real) := ~ (forall y0 : real, forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1))).
Definition term124 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term84 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul (real_sub x0 x1) x2).
Definition term67 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))).
Definition term107 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term90 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term110 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term47 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2)).
Definition term27 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2))) x0).
Definition term98 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term65 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term62 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term116 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term115 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := real_sub (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))) (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))).
Definition term8 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0))) x2).
Definition term123 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term43 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term42 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term125 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2)))) -> False.
Definition term12 (x0 : real) (x1 : real) := exists y0 : real, ~ ((real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0))).
Definition term76 := real_mul (real_of_num (NUMERAL 0)).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1))) x1.
Definition term39 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term102 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term69 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2)) (real_mul x1 x2)).
Definition term68 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x2)) (real_mul x1 x2)).
Definition term37 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term20 (x0 : real) := fun y0 : real => exists y1 : real, ~ ((real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1))).
Definition term63 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term114 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term41 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term108 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term96 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term126 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2)))) -> False) -> forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2)).
Definition term4 (x0 : real) (x1 : real) := fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0)).
Definition term32 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2)).
Definition term82 (x0 : real) (x1 : real) (x2 : real) := real_neg (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2))).
Definition term113 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term54 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term50 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul x0 x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))).
Definition term24 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2)).
Definition term18 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul (real_sub x0 y0) y1) = (real_sub (real_mul x0 y1) (real_mul y0 y1))) x1).
Definition term100 := fun y0 : real => exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term29 := fun y0 : real => exists y1 : real, exists y2 : real, ~ ((real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2))).
Definition term57 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term61 := real_of_num (NUMERAL (BIT1 0)).
Definition term64 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul x0 x1).
Definition term117 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term86 (x0 : real) (x1 : real) (x2 : real) := @eq real (real_neg (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2)))).
Definition term80 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul x0 x1).
Definition term89 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2)))) (real_of_num (NUMERAL 0)).
Definition term53 (x0 : real) (x1 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_mul x0 x1).
Definition term10 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul (real_sub x0 x1) y1) = (real_sub (real_mul x0 y1) (real_mul x1 y1))) y0).
Definition term5 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0))) x2.
Definition term87 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_neg (real_sub (real_mul (real_sub x0 x1) x2) (real_sub (real_mul x0 x2) (real_mul x1 x2)))).
Definition term94 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term77 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term55 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term112 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term81 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term17 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_sub x0 x1) y0) = (real_sub (real_mul x0 y0) (real_mul x1 y0)).
Definition term9 (x0 : real) (x1 : real) (x2 : real) := ~ ((real_mul (real_sub x0 x1) x2) = (real_sub (real_mul x0 x2) (real_mul x1 x2))).
Definition term34 (x0 : real) (x1 : real) := real_mul (real_sub x0 x1).
Definition term33 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term74 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term79 := real_add (real_of_num (NUMERAL 0)).
Definition term121 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_sub y0 y1) y2) = (real_sub (real_mul y0 y2) (real_mul y1 y2))) x0.
Definition term104 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term66 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x2)) (real_mul x1 x2).
Definition term58 := NUMERAL (BIT1 0).
Definition term51 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x2)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x1 x2))).
Definition term109 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term97 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term119 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term88 := real_gt (real_of_num (NUMERAL 0)).
