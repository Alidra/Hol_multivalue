Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term79 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term45 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x1) (real_of_num (NUMERAL 0))).
Definition term98 (x0 : real) := real_lt (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term22 := real_of_num (NUMERAL 0).
Definition term92 (x0 : real) (x1 : real) := (real_lt (real_abs x0) x1) -> real_lt x0 x1.
Definition term54 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term12 := forall y0 : real, (real_abs y0) = (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term9 := fun y0 : real => (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (real_abs y0).
Definition term6 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> real_lt (sqrt x0) (sqrt x1).
Definition term58 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term73 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term101 (x0 : real) (x1 : real) := (real_lt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1) -> real_lt (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1).
Definition term7 := (forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) -> forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1).
Definition term93 (x0 : real) (x1 : real) := ((real_lt (real_abs x0) x1) -> real_lt x0 x1) -> real_lt x0 x1.
Definition term72 (x0 : real) (x1 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term104 (x0 : real) (x1 : real) := (real_lt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1) -> real_lt x0 (sqrt x1).
Definition term86 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term48 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term42 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) (real_of_num (NUMERAL 0)).
Definition term95 (x0 : real) (x1 : real) := real_lt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) x1.
Definition term14 (x0 : real) (x1 : real) := ~ ((real_lt (real_abs x0) x1) -> real_lt x0 x1).
Definition term31 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term100 (x0 : real) (x1 : real) := real_lt (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) (sqrt x1).
Definition term94 (x0 : real) (x1 : real) := ((real_lt (real_abs x0) x1) -> real_lt x0 x1) -> (real_lt (real_abs x0) x1) -> real_lt x0 x1.
Definition term103 (x0 : real) (x1 : real) := real_lt x0 (sqrt x1).
Definition term27 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term17 (x0 : real) (x1 : real) := real_gt (real_sub x0 (real_abs x1)) (real_of_num (NUMERAL 0)).
Definition term36 (x0 : real) (x1 : real) (x2 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) x2) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) x2).
Definition term64 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term11 := forall y0 : real, (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (real_abs y0).
Definition term37 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)) (real_of_num (NUMERAL 0))).
Definition term51 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term106 := forall y0 : real, forall y1 : real, (real_lt (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) y1) -> real_lt y0 (sqrt y1).
Definition term0 := forall y0 : real, forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1).
Definition term65 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term41 (x0 : real) (x1 : real) := real_gt (real_add x0 x1).
Definition term35 (x0 : real) (x1 : real) (x2 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))) x2.
Definition term96 (x0 : real) (x1 : real) := (real_lt (real_abs x0) (sqrt x1)) -> real_lt x0 (sqrt x1).
Definition term46 (x0 : real) (x1 : real) := and ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)))).
Definition term67 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term40 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1)).
Definition term30 (x0 : real) (x1 : real) := real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term77 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term102 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term89 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term24 (x0 : real) (x1 : real) := ~ (real_lt x0 x1).
Definition term88 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term82 (x0 : real) := real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term44 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term84 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term55 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term20 (x0 : real) (x1 : real) := real_gt (real_sub x0 (real_abs x1)).
Definition term71 (x0 : real) (x1 : real) := real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term61 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))).
Definition term8 (x0 : real) := sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term1 (x0 : real) := (fun y0 : real => forall y1 : real, (real_lt y0 y1) -> real_lt (sqrt y0) (sqrt y1)) x0.
Definition term49 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term53 := S (Nat.add 0 0).
Definition term75 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term19 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1)).
Definition term76 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term60 (x0 : real) (x1 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term18 (x0 : real) (x1 : real) := real_sub x0 (real_abs x1).
Definition term29 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1).
Definition term13 (x0 : real) := (fun y0 : real => (real_abs y0) = (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term59 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term80 := real_mul (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term66 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))).
Definition term3 (x0 : real) (x1 : real) := (fun y0 : real => (real_lt x0 y0) -> real_lt (sqrt x0) (sqrt y0)) x1.
Definition term2 (x0 : real) := forall y0 : real, (real_lt x0 y0) -> real_lt (sqrt x0) (sqrt y0).
Definition term16 (x0 : real) (x1 : real) := real_lt (real_abs x0) x1.
Definition term47 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real) (x1 : real) := real_lt (sqrt x0) (sqrt x1).
Definition term57 := real_of_num (NUMERAL (BIT1 0)).
Definition term15 (x0 : real) (x1 : real) := (real_lt (real_abs x0) x1) /\ (~ (real_lt x0 x1)).
Definition term21 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))).
Definition term43 (x0 : real) (x1 : real) := real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term99 (x0 : real) (x1 : real) := real_lt (real_abs x0) (sqrt x1).
Definition term81 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term105 (x0 : real) := forall y0 : real, (real_lt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) y0) -> real_lt x0 (sqrt y0).
Definition term56 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term90 (x0 : real) (x1 : real) := (~ ((real_lt (real_abs x0) x1) -> real_lt x0 x1)) -> False.
Definition term85 := real_add (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term23 (x0 : real) (x1 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))) (real_of_num (NUMERAL 0)).
Definition term97 (x0 : real) := real_lt (real_abs x0).
Definition term39 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_of_num (NUMERAL (BIT1 0))) x1).
Definition term26 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term78 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term4 (x0 : real) (x1 : real) := (real_lt x0 x1) -> real_lt (sqrt x0) (sqrt x1).
Definition term63 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1))) (real_of_num (NUMERAL 0)).
Definition term83 := real_add (real_of_num (NUMERAL 0)).
Definition term91 (x0 : real) (x1 : real) := ((~ ((real_lt (real_abs x0) x1) -> real_lt x0 x1)) -> False) -> (real_lt (real_abs x0) x1) -> real_lt x0 x1.
Definition term70 (x0 : real) (x1 : real) := ((real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term10 := fun y0 : real => (real_abs y0) = (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term52 := NUMERAL (BIT1 0).
Definition term69 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term62 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term74 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term50 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term33 (x0 : real) (x1 : real) := and (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))) (real_of_num (NUMERAL 0))).
Definition term68 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term34 (x0 : real) (x1 : real) := (real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_abs x1))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term32 (x0 : real) (x1 : real) := and (real_lt (real_abs x0) x1).
Definition term25 (x0 : real) (x1 : real) := real_ge (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term87 := real_gt (real_of_num (NUMERAL 0)).
