Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term92 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term11 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ~ ((real_sub (real_add x0 x2) (real_add x1 y0)) = (real_add (real_sub x0 x1) (real_sub x2 y0))).
Definition term74 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term115 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := or (real_gt (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3))) (real_of_num (NUMERAL 0))).
Definition term100 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term90 := real_of_num (NUMERAL 0).
Definition term51 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 x1).
Definition term135 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term47 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
Definition term129 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term2 (x0 : real) (x1 : real) (x2 : real) := ~ (forall y0 : real, (real_sub (real_add x0 x2) (real_add x1 y0)) = (real_add (real_sub x0 x1) (real_sub x2 y0))).
Definition term105 := real_neg (real_of_num (NUMERAL 0)).
Definition term60 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))))).
Definition term114 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3))) (real_of_num (NUMERAL 0)).
Definition term4 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => (real_sub (real_add x0 x2) (real_add x1 y0)) = (real_add (real_sub x0 x1) (real_sub x2 y0)).
Definition term5 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (fun y0 : real => (real_sub (real_add x0 x2) (real_add x1 y0)) = (real_add (real_sub x0 x1) (real_sub x2 y0))) x3.
Definition term97 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 x2)).
Definition term80 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term18 (x0 : real) (x1 : real) (x2 : real) := ~ ((fun y0 : real => forall y1 : real, (real_sub (real_add x0 x1) (real_add y0 y1)) = (real_add (real_sub x0 y0) (real_sub x1 y1))) x2).
Definition term55 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)).
Definition term127 (x0 : Prop) := exists y0 : real, x0.
Definition term142 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term107 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term151 := forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3)).
Definition term35 (x0 : real) := forall y0 : real, forall y1 : real, forall y2 : real, (real_sub (real_add x0 y0) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub y0 y2)).
Definition term26 (x0 : real) (x1 : real) := forall y0 : real, forall y1 : real, (real_sub (real_add x0 x1) (real_add y0 y1)) = (real_add (real_sub x0 y0) (real_sub x1 y1)).
Definition term67 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term102 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term125 := exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term123 := exists y0 : real, exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term121 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term39 := exists y0 : real, exists y1 : real, exists y2 : real, exists y3 : real, ~ ((real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3))).
Definition term30 (x0 : real) := exists y0 : real, exists y1 : real, exists y2 : real, ~ ((real_sub (real_add x0 y0) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub y0 y2))).
Definition term21 (x0 : real) (x1 : real) := exists y0 : real, exists y1 : real, ~ ((real_sub (real_add x0 x1) (real_add y0 y1)) = (real_add (real_sub x0 y0) (real_sub x1 y1))).
Definition term71 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term144 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term32 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, forall y4 : real, (real_sub (real_add y1 y2) (real_add y3 y4)) = (real_add (real_sub y1 y3) (real_sub y2 y4))) y0).
Definition term23 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_sub (real_add x0 y1) (real_add y2 y3)) = (real_add (real_sub x0 y2) (real_sub y1 y3))) y0).
Definition term14 (x0 : real) (x1 : real) := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_sub (real_add x0 x1) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub x1 y2))) y0).
Definition term3 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, ~ ((fun y1 : real => (real_sub (real_add x0 x2) (real_add x1 y1)) = (real_add (real_sub x0 x1) (real_sub x2 y1))) y0).
Definition term84 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term17 (x0 : real) (x1 : real) (x2 : real) := forall y0 : real, (real_sub (real_add x0 x2) (real_add x1 y0)) = (real_add (real_sub x0 x1) (real_sub x2 y0)).
Definition term37 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, forall y4 : real, (real_sub (real_add y1 y2) (real_add y3 y4)) = (real_add (real_sub y1 y3) (real_sub y2 y4))) y0).
Definition term28 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, forall y3 : real, (real_sub (real_add x0 y1) (real_add y2 y3)) = (real_add (real_sub x0 y2) (real_sub y1 y3))) y0).
Definition term19 (x0 : real) (x1 : real) := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_sub (real_add x0 x1) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub x1 y2))) y0).
Definition term54 (x0 : real) (x1 : real) := real_add (real_add x0 x1).
Definition term15 (x0 : real) (x1 : real) := fun y0 : real => forall y1 : real, (real_sub (real_add x0 x1) (real_add y0 y1)) = (real_add (real_sub x0 y0) (real_sub x1 y1)).
Definition term89 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term75 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term117 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term40 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := (real_gt (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3)))) (real_of_num (NUMERAL 0))).
Definition term113 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3))).
Definition term130 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term146 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term31 := ~ (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3))).
Definition term22 (x0 : real) := ~ (forall y0 : real, forall y1 : real, forall y2 : real, (real_sub (real_add x0 y0) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub y0 y2))).
Definition term13 (x0 : real) (x1 : real) := ~ (forall y0 : real, forall y1 : real, (real_sub (real_add x0 x1) (real_add y0 y1)) = (real_add (real_sub x0 y0) (real_sub x1 y1))).
Definition term148 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term106 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term104 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_neg (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3))).
Definition term52 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term109 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_neg (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3)))).
Definition term64 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term131 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term98 (x0 : real) (x1 : real) (x2 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)) (real_add x1 x2)).
Definition term112 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term134 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term50 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x2 x3)).
Definition term79 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term95 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term36 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3))) x0).
Definition term120 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term101 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term77 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term140 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term139 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term82 (x0 : real) (x1 : real) (x2 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 x2).
Definition term59 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term147 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term57 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term88 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term8 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((fun y0 : real => (real_sub (real_add x0 x2) (real_add x1 y0)) = (real_add (real_sub x0 x1) (real_sub x2 y0))) x3).
Definition term53 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term149 := (~ (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3)))) -> False.
Definition term12 (x0 : real) (x1 : real) (x2 : real) := exists y0 : real, ~ ((real_sub (real_add x0 x2) (real_add x1 y0)) = (real_add (real_sub x0 x1) (real_sub x2 y0))).
Definition term86 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 x3))).
Definition term58 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3)).
Definition term93 := real_mul (real_of_num (NUMERAL 0)).
Definition term45 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))).
Definition term46 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term126 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term62 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term20 (x0 : real) (x1 : real) := fun y0 : real => exists y1 : real, ~ ((real_sub (real_add x0 x1) (real_add y0 y1)) = (real_add (real_sub x0 y0) (real_sub x1 y1))).
Definition term78 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term138 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term132 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term118 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term49 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3))).
Definition term44 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add x2 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)).
Definition term150 := ((~ (forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3)))) -> False) -> forall y0 : real, forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3)).
Definition term7 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_sub x0 x1) (real_sub x2 x3).
Definition term16 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => forall y1 : real, (real_sub (real_add x0 x1) (real_add y0 y1)) = (real_add (real_sub x0 y0) (real_sub x1 y1))) x2.
Definition term137 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term69 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term33 := fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3)).
Definition term24 (x0 : real) := fun y0 : real => forall y1 : real, forall y2 : real, (real_sub (real_add x0 y0) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub y0 y2)).
Definition term27 (x0 : real) (x1 : real) := ~ ((fun y0 : real => forall y1 : real, forall y2 : real, (real_sub (real_add x0 y0) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub y0 y2))) x1).
Definition term43 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term63 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2))).
Definition term124 := fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term122 := fun y0 : real => exists y1 : real, exists y2 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term38 := fun y0 : real => exists y1 : real, exists y2 : real, exists y3 : real, ~ ((real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3))).
Definition term29 (x0 : real) := fun y0 : real => exists y1 : real, exists y2 : real, ~ ((real_sub (real_add x0 y0) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub y0 y2))).
Definition term42 (x0 : real) (x1 : real) := real_add (real_sub x0 x1).
Definition term72 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term76 := real_of_num (NUMERAL (BIT1 0)).
Definition term81 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term141 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term94 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term68 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term111 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_gt (real_neg (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3)))) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := @eq real (real_neg (real_sub (real_sub (real_add x0 x2) (real_add x1 x3)) (real_add (real_sub x0 x1) (real_sub x2 x3)))).
Definition term10 (x0 : real) (x1 : real) (x2 : real) := fun y0 : real => ~ ((fun y1 : real => (real_sub (real_add x0 x2) (real_add x1 y1)) = (real_add (real_sub x0 x1) (real_sub x2 y1))) y0).
Definition term25 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_sub (real_add x0 y0) (real_add y1 y2)) = (real_add (real_sub x0 y1) (real_sub y0 y2))) x1.
Definition term9 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := ~ ((real_sub (real_add x0 x2) (real_add x1 x3)) = (real_add (real_sub x0 x1) (real_sub x2 x3))).
Definition term116 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term70 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term136 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term65 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term103 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term61 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))).
Definition term56 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_sub (real_add x0 x1) (real_add x2 x3)).
Definition term41 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term91 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term99 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add x0 x1).
Definition term96 := real_add (real_of_num (NUMERAL 0)).
Definition term145 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term85 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_add x0 (real_add x1 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x3)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 x3))).
Definition term34 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, forall y3 : real, (real_sub (real_add y0 y1) (real_add y2 y3)) = (real_add (real_sub y0 y2) (real_sub y1 y3))) x0.
Definition term128 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term73 := NUMERAL (BIT1 0).
Definition term133 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term119 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term83 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add x2 x3)).
Definition term87 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term143 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term66 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term110 := real_gt (real_of_num (NUMERAL 0)).
Definition term6 (x0 : real) (x1 : real) (x2 : real) (x3 : real) := real_sub (real_add x0 x1) (real_add x2 x3).
Definition term48 (x0 : real) (x1 : real) (x2 : real) := real_add x0 (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x2)).
