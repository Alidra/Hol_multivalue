Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term30 (x0 : real) (x1 : real) := real_mul (real_add x0 x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term49 (x0 : real) (x1 : real) := real_add (real_mul x0 x1).
Definition term61 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term0 (x0 : real -> Prop) := ~ (all x0).
Definition term11 (x0 : real) := fun y0 : real => ~ ((real_mul (real_add x0 y0) (real_sub x0 y0)) = (real_sub (real_mul x0 x0) (real_mul y0 y0))).
Definition term68 (x0 : real) (x1 : real) := real_sub (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term80 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term43 (x0 : real) (x1 : real) := real_mul x1 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term108 (x0 : real) (x1 : real) := or (real_gt (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1))) (real_of_num (NUMERAL 0))).
Definition term58 := real_of_num (NUMERAL 0).
Definition term6 (x0 : real) (x1 : real) := real_mul (real_add x0 x1) (real_sub x0 x1).
Definition term9 (x0 : real) (x1 : real) := ~ ((real_mul (real_add x0 x1) (real_sub x0 x1)) = (real_sub (real_mul x0 x0) (real_mul x1 x1))).
Definition term64 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul x0 x1)).
Definition term92 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term124 (x0 : real) := (fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0.
Definition term35 (x0 : real) (x1 : real) := real_mul x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term118 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := (exists y0 : a0, x0 y0) \/ (exists y0 : a0, x1 y0).
Definition term48 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term87 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term2 (x0 : real) := ~ (forall y0 : real, (real_mul (real_add x0 y0) (real_sub x0 y0)) = (real_sub (real_mul x0 x0) (real_mul y0 y0))).
Definition term41 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term98 := real_neg (real_of_num (NUMERAL 0)).
Definition term46 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x0).
Definition term24 (x0 : real) := real_sub (real_mul x0 x0).
Definition term56 (x0 : real) (x1 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term8 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_mul (real_add x0 y0) (real_sub x0 y0)) = (real_sub (real_mul x0 x0) (real_mul y0 y0))) x1).
Definition term107 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1))) (real_of_num (NUMERAL 0)).
Definition term106 (x0 : real) (x1 : real) := real_gt (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1))).
Definition term95 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term116 (x0 : Prop) := exists y0 : real, x0.
Definition term131 := exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term100 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term140 := forall y0 : real, forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1)).
Definition term73 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term114 := exists y0 : real, exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term21 := exists y0 : real, exists y1 : real, ~ ((real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1))).
Definition term78 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term133 := or (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term54 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul x0 x1)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term25 (x0 : real) := real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term42 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))).
Definition term14 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_mul (real_add y1 y2) (real_sub y1 y2)) = (real_sub (real_mul y1 y1) (real_mul y2 y2))) y0).
Definition term3 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_mul (real_add x0 y1) (real_sub x0 y1)) = (real_sub (real_mul x0 x0) (real_mul y1 y1))) y0).
Definition term66 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term31 (x0 : real) (x1 : real) := real_add (real_mul x0 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_mul x1 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term17 (x0 : real) := forall y0 : real, (real_mul (real_add x0 y0) (real_sub x0 y0)) = (real_sub (real_mul x0 x0) (real_mul y0 y0)).
Definition term7 (x0 : real) (x1 : real) := real_sub (real_mul x0 x0) (real_mul x1 x1).
Definition term19 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_mul (real_add y1 y2) (real_sub y1 y2)) = (real_sub (real_mul y1 y1) (real_mul y2 y2))) y0).
Definition term32 (x0 : real) (x1 : real) := real_mul x0 (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term5 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_add x0 y0) (real_sub x0 y0)) = (real_sub (real_mul x0 x0) (real_mul y0 y0))) x1.
Definition term15 := fun y0 : real => forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1)).
Definition term57 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term81 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term86 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term110 := (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term23 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term22 (x0 : real) (x1 : real) := (real_gt (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1)))) (real_of_num (NUMERAL 0))).
Definition term119 (x0 : real -> Prop) (x1 : real -> Prop) := exists y0 : real, (x0 y0) \/ (x1 y0).
Definition term135 := (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term13 := ~ (forall y0 : real, forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1))).
Definition term137 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term99 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term71 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term102 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1)))).
Definition term120 (x0 : real -> Prop) (x1 : real -> Prop) := (exists y0 : real, x0 y0) \/ (exists y0 : real, x1 y0).
Definition term105 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term123 := fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term51 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1))) (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term52 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))))).
Definition term18 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1))) x0).
Definition term113 := fun y0 : real => exists y1 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term83 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term97 (x0 : real) (x1 : real) := real_neg (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1))).
Definition term129 := @eq Prop (exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)))).
Definition term128 := @eq Prop (exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0)).
Definition term1 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term93 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term33 (x0 : real) (x1 : real) := real_add (real_mul x0 x0) (real_mul x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1))) x0.
Definition term85 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term136 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term47 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term53 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term37 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term138 := (~ (forall y0 : real, forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1)))) -> False.
Definition term12 (x0 : real) := exists y0 : real, ~ ((real_mul (real_add x0 y0) (real_sub x0 y0)) = (real_sub (real_mul x0 x0) (real_mul y0 y0))).
Definition term44 (x0 : real) (x1 : real) := real_add (real_mul x1 x0) (real_mul x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term38 (x0 : real) := real_add (real_mul x0 x0).
Definition term62 := real_mul (real_of_num (NUMERAL 0)).
Definition term27 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term34 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term115 (a0 : Type') (x0 : Prop) := exists y0 : a0, x0.
Definition term91 (x0 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term20 := fun y0 : real => exists y1 : real, ~ ((real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1))).
Definition term84 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term127 := fun y0 : real => ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term36 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1).
Definition term121 := exists y0 : real, ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ ((fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term111 := fun y0 : real => (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term139 := ((~ (forall y0 : real, forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1)))) -> False) -> forall y0 : real, forall y1 : real, (real_mul (real_add y0 y1) (real_sub y0 y1)) = (real_sub (real_mul y0 y0) (real_mul y1 y1)).
Definition term26 (x0 : real) (x1 : real) := real_sub (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term50 (x0 : real) (x1 : real) := real_add (real_mul x0 x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term126 (x0 : real) := ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0) \/ ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term76 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term29 (x0 : real) (x1 : real) := real_mul (real_add x0 x1).
Definition term45 (x0 : real) := real_mul x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term79 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term82 := real_of_num (NUMERAL (BIT1 0)).
Definition term70 (x0 : real) (x1 : real) := real_sub (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term69 (x0 : real) (x1 : real) := real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1)).
Definition term130 := fun y0 : real => (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0.
Definition term55 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)) (real_mul x0 x1).
Definition term94 (x0 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term88 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term72 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term104 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1)))) (real_of_num (NUMERAL 0)).
Definition term101 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)) (real_sub (real_mul x0 x0) (real_mul x1 x1)))).
Definition term40 (x0 : real) (x1 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul x0 x1)).
Definition term10 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_mul (real_add x0 y1) (real_sub x0 y1)) = (real_sub (real_mul x0 x0) (real_mul y1 y1))) y0).
Definition term109 := or (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term39 (x0 : real) := real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term63 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term77 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term125 (x0 : real) := or ((fun y0 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) x0).
Definition term96 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term4 (x0 : real) := fun y0 : real => (real_mul (real_add x0 y0) (real_sub x0 y0)) = (real_sub (real_mul x0 x0) (real_mul y0 y0)).
Definition term67 (x0 : real) (x1 : real) := real_sub (real_mul (real_add x0 x1) (real_sub x0 x1)).
Definition term28 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term75 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term59 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term74 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term65 := real_add (real_of_num (NUMERAL 0)).
Definition term134 := or (exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term117 (a0 : Type') (x0 : a0 -> Prop) (x1 : a0 -> Prop) := exists y0 : a0, (x0 y0) \/ (x1 y0).
Definition term60 := NUMERAL (BIT1 0).
Definition term122 := (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0) \/ (exists y0 : real, (fun y1 : real => real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) y0).
Definition term112 := exists y0 : real, (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0))).
Definition term132 := exists y0 : real, real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term103 := real_gt (real_of_num (NUMERAL 0)).
Definition term90 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term89 (x0 : real) (x1 : real) := real_add (real_add (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
