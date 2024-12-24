Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term31 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term70 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term6 (x0 : real -> Prop) := ~ (all x0).
Definition term32 := real_of_num (NUMERAL 0).
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) -> ~ (real_lt y0 x0)) x1.
Definition term51 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term64 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term36 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term8 (x0 : real) := ~ (forall y0 : real, (real_lt x0 y0) -> ~ (real_lt y0 x0)).
Definition term63 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term77 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term12 (x0 : real) (x1 : real) := (real_lt x1 x0) -> ~ (real_lt x0 x1).
Definition term35 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term13 (x0 : real) (x1 : real) := ~ ((fun y0 : real => (real_lt x0 y0) -> ~ (real_lt y0 x0)) x1).
Definition term3 (x0 : real) (x1 : real) := (real_lt x1 x0) /\ (real_lt x0 x1).
Definition term28 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term56 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term37 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term44 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term83 := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0).
Definition term41 := exists y0 : real, exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term25 := exists y0 : real, exists y1 : real, (real_lt y0 y1) /\ (real_lt y1 y0).
Definition term57 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term18 := exists y0 : real, ~ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) -> ~ (real_lt y2 y1)) y0).
Definition term9 (x0 : real) := exists y0 : real, ~ ((fun y1 : real => (real_lt x0 y1) -> ~ (real_lt y1 x0)) y0).
Definition term1 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term34 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term23 := fun y0 : real => ~ ((fun y1 : real => forall y2 : real, (real_lt y1 y2) -> ~ (real_lt y2 y1)) y0).
Definition term59 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term68 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term17 := ~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0)).
Definition term80 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term5 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term4 (x0 : real) (x1 : real) := ~ ((real_lt x1 x0) -> ~ (real_lt x0 x1)).
Definition term79 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term16 (x0 : real) := exists y0 : real, (real_lt x0 y0) /\ (real_lt y0 x0).
Definition term73 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term22 (x0 : real) := ~ ((fun y0 : real => forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0)) x0).
Definition term40 := fun y0 : real => exists y1 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0) y1) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add y0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y1)) (real_of_num (NUMERAL 0))).
Definition term75 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term62 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term54 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term7 (x0 : real -> Prop) := exists y0 : real, ~ (x0 y0).
Definition term20 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0)) x0.
Definition term42 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term46 := S (Nat.add 0 0).
Definition term66 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term67 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term81 := (~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0))) -> False.
Definition term53 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term52 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term71 := real_mul (real_of_num (NUMERAL 0)).
Definition term29 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term2 (x0 : real) (x1 : real) := (real_lt x1 x0) /\ (~ (~ (real_lt x0 x1))).
Definition term15 (x0 : real) := fun y0 : real => (real_lt x0 y0) /\ (real_lt y0 x0).
Definition term82 := ((~ (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0))) -> False) -> forall y0 : real, forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0).
Definition term26 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term0 (x0 : real) (x1 : real) := ~ (~ (real_lt x0 x1)).
Definition term58 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term24 := fun y0 : real => exists y1 : real, (real_lt y0 y1) /\ (real_lt y1 y0).
Definition term50 := real_of_num (NUMERAL (BIT1 0)).
Definition term39 (x0 : real) := exists y0 : real, (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term72 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term21 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> ~ (real_lt y0 x0).
Definition term14 (x0 : real) := fun y0 : real => ~ ((fun y1 : real => (real_lt x0 y1) -> ~ (real_lt y1 x0)) y0).
Definition term76 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term27 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term69 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term38 (x0 : real) := fun y0 : real => (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) y0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) y0)) (real_of_num (NUMERAL 0))).
Definition term55 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term30 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term74 := real_add (real_of_num (NUMERAL 0)).
Definition term10 (x0 : real) := fun y0 : real => (real_lt x0 y0) -> ~ (real_lt y0 x0).
Definition term61 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term49 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term45 := NUMERAL (BIT1 0).
Definition term60 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term48 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term65 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term43 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term19 := fun y0 : real => forall y1 : real, (real_lt y0 y1) -> ~ (real_lt y1 y0).
Definition term47 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term78 := real_gt (real_of_num (NUMERAL 0)).
