Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term53 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term112 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term7 (x0 : real -> Prop) := ~ (all x0).
Definition term43 := Nat.pow (BIT1 0) (NUMERAL (BIT0 (BIT1 0))).
Definition term2 (x0 : real) (x1 : real) := and (~ (x0 = x1)).
Definition term55 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub x0 x1)) (real_of_num (NUMERAL 0)).
Definition term54 := real_of_num (NUMERAL 0).
Definition term90 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term130 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term126 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term85 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term93 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term9 (x0 : real) := ~ (forall y0 : real, (x0 = y0) \/ ((real_lt x0 y0) \/ (real_lt y0 x0))).
Definition term106 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term119 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term0 (x0 : real) (x1 : real) := ~ ((real_lt x1 x0) \/ (real_lt x0 x1)).
Definition term11 (x0 : real) := fun y0 : real => (x0 = y0) \/ ((real_lt x0 y0) \/ (real_lt y0 x0)).
Definition term60 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term14 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (x0 = y0) \/ ((real_lt x0 y0) \/ (real_lt y0 x0))) x1).
Definition term51 (x0 : real) (x1 : real) := @eq real (real_neg (real_sub x0 x1)).
Definition term70 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term73 (x0 : real) (x1 : real) := (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term50 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term13 (x0 : real) (x1 : real) := (x1 = x0) \/ ((real_lt x1 x0) \/ (real_lt x0 x1)).
Definition term99 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term63 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term80 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))))).
Definition term3 (x0 : real) (x1 : real) := (~ (x1 = x0)) /\ (~ ((real_lt x1 x0) \/ (real_lt x0 x1))).
Definition term88 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term141 := forall y0 : real, forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0)).
Definition term36 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term137 (x0 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term84 := exists y0 : real, exists y1 : real, ((real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))))).
Definition term79 := exists y0 : real, exists y1 : real, ((real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))).
Definition term26 := exists y0 : real, exists y1 : real, (~ (y0 = y1)) /\ ((~ (real_lt y0 y1)) /\ (~ (real_lt y1 y0))).
Definition term40 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term100 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term52 (x0 : real) (x1 : real) := real_gt (real_neg (real_sub x0 x1)).
Definition term134 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term19 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (y1 = y2) \/ ((real_lt y1 y2) \/ (real_lt y2 y1))) y0).
Definition term10 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (x0 = y1) \/ ((real_lt x0 y1) \/ (real_lt y1 x0))) y0).
Definition term58 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term69 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term61 (x0 : real) (x1 : real) := or (real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0))).
Definition term24 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (y1 = y2) \/ ((real_lt y1 y2) \/ (real_lt y2 y1))) y0).
Definition term20 := fun y0 : real => forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0)).
Definition term68 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term110 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term44 := Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term74 (x0 : real) (x1 : real) := and ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term27 (x0 : real) (x1 : real) := ~ (x0 = x1).
Definition term18 := ~ (forall y0 : real, forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0))).
Definition term122 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term64 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term124 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term121 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term48 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term115 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term23 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0))) x0).
Definition term83 := fun y0 : real => exists y1 : real, ((real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))))).
Definition term78 := fun y0 : real => exists y1 : real, ((real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0)))).
Definition term25 := fun y0 : real => exists y1 : real, (~ (y0 = y1)) /\ ((~ (real_lt y0 y1)) /\ (~ (real_lt y1 y0))).
Definition term117 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term46 := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))).
Definition term91 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term105 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term96 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term8 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term81 (x0 : real) := fun y0 : real => ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))))).
Definition term76 (x0 : real) := fun y0 : real => ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))).
Definition term21 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0))) x0.
Definition term86 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term28 (x0 : real) (x1 : real) := (real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 x1)) (real_of_num (NUMERAL 0))).
Definition term67 (x0 : real) (x1 : real) := real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term89 := S (Nat.add 0 0).
Definition term109 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term127 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term34 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term139 := (~ (forall y0 : real, forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0)))) -> False.
Definition term132 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term71 (x0 : real) (x1 : real) := and (~ (real_lt x0 x1)).
Definition term95 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term12 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) \/ ((real_lt x0 y0) \/ (real_lt y0 x0))) x1.
Definition term136 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term66 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term16 (x0 : real) := fun y0 : real => (~ (x0 = y0)) /\ ((~ (real_lt x0 y0)) /\ (~ (real_lt y0 x0))).
Definition term131 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term94 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term113 := real_mul (real_of_num (NUMERAL 0)).
Definition term22 (x0 : real) := forall y0 : real, (x0 = y0) \/ ((real_lt x0 y0) \/ (real_lt y0 x0)).
Definition term35 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term47 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term77 (x0 : real) := exists y0 : real, ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0)))).
Definition term125 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term140 := ((~ (forall y0 : real, forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0)))) -> False) -> forall y0 : real, forall y1 : real, (y0 = y1) \/ ((real_lt y0 y1) \/ (real_lt y1 y0)).
Definition term59 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term62 (x0 : real) (x1 : real) := or (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term1 (x0 : real) (x1 : real) := (~ (real_lt x1 x0)) /\ (~ (real_lt x0 x1)).
Definition term101 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term38 (x0 : nat) (x1 : nat) := real_mul (real_neg (real_of_num x0)) (real_neg (real_of_num x1)).
Definition term17 (x0 : real) := exists y0 : real, (~ (x0 = y0)) /\ ((~ (real_lt x0 y0)) /\ (~ (real_lt y0 x0))).
Definition term75 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) \/ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term4 (x0 : real) (x1 : real) := (~ (x1 = x0)) /\ ((~ (real_lt x1 x0)) /\ (~ (real_lt x0 x1))).
Definition term41 := real_of_num (Nat.mul (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0))).
Definition term45 := real_of_num (NUMERAL (BIT1 0)).
Definition term49 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term114 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term37 (x0 : real) := real_mul (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_neg (real_of_num (NUMERAL (BIT1 0))))) x0.
Definition term15 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (x0 = y1) \/ ((real_lt x0 y1) \/ (real_lt y1 x0))) y0).
Definition term123 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))).
Definition term82 (x0 : real) := exists y0 : real, ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))))) \/ ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ ((real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))))).
Definition term72 (x0 : real) (x1 : real) := and (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term6 (x0 : real) (x1 : real) := (real_lt x1 x0) \/ (real_lt x0 x1).
Definition term30 (x0 : real) (x1 : real) := real_neg (real_sub x0 x1).
Definition term92 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term39 (x0 : nat) (x1 : nat) := real_of_num (Nat.mul x0 x1).
Definition term118 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term138 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term32 (x0 : real) (x1 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term5 (x0 : real) (x1 : real) := ~ ((x1 = x0) \/ ((real_lt x1 x0) \/ (real_lt x0 x1))).
Definition term29 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term111 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term133 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term98 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term57 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term116 := real_add (real_of_num (NUMERAL 0)).
Definition term135 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term129 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term104 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term56 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term42 := NUMERAL (BIT1 0).
Definition term31 (x0 : real) (x1 : real) := real_neg (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term103 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term97 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term87 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term102 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term128 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term65 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term120 := real_gt (real_of_num (NUMERAL 0)).
