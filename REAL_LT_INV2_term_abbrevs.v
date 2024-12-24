Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term66 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term216 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x1) /\ (real_lt x1 x0)) -> real_lt (real_inv x0) (real_inv x1).
Definition term120 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term17 := forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term168 (x0 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term149 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term107 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term85 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term0 (x0 : real) (x1 : real) (x2 : real) := real_mul x0 (real_mul x1 x2).
Definition term184 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> ~ (x1 = (real_of_num (NUMERAL 0))).
Definition term145 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term183 (x0 : real) (x1 : real) := ((~ (((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> ~ (x1 = (real_of_num (NUMERAL 0))))) -> False) -> ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> ~ (x1 = (real_of_num (NUMERAL 0))).
Definition term170 (x0 : real) (x1 : real) := ((~ (((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> ~ (x1 = (real_of_num (NUMERAL 0))))) -> False) -> ((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> ~ (x1 = (real_of_num (NUMERAL 0))).
Definition term51 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 x1).
Definition term67 := real_of_num (NUMERAL 0).
Definition term192 (x0 : real) (x1 : real) := real_lt (real_mul (real_mul (real_inv x1) x0) x1).
Definition term136 (x0 : real) (x1 : real) := real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term90 (x0 : real) (x1 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))).
Definition term130 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term180 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x1).
Definition term164 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term28 (x0 : real) (x1 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term189 (x0 : real) (x1 : real) := real_mul (real_inv x1) (real_mul x0 x1).
Definition term194 (x0 : real) (x1 : real) := real_mul (real_mul (real_inv x0) x0) x1.
Definition term190 (x0 : real) (x1 : real) := real_mul (real_mul (real_inv x1) x0) x1.
Definition term127 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))).
Definition term94 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))).
Definition term211 (x0 : real) (x1 : real) := real_mul x0 (real_mul (real_inv x1) x1).
Definition term79 (x0 : real) (x1 : real) := and (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term48 := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1) -> forall y0 : real, forall y1 : real, (exists y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1.
Definition term33 := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1)) -> forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term153 (x0 : real) (x1 : real) := (~ (((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1))) -> False.
Definition term32 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term87 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term15 (x0 : real) := forall y0 : real, (real_mul x0 y0) = (real_mul y0 x0).
Definition term198 (x0 : real) (x1 : real) := real_lt (real_mul (real_mul (real_inv x1) x0) x1) x1.
Definition term161 (x0 : real) := @eq real (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term165 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_neg (real_of_num (NUMERAL (BIT1 0)))).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 y0) = (real_mul y0 x0)) x1.
Definition term93 (x0 : real) (x1 : real) := (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) \/ (((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0)))).
Definition term38 (x0 : real) (x1 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul x0 y0) (real_mul x1 y0))) -> real_lt x0 x1.
Definition term76 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term158 (x0 : real) (x1 : real) := ((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) /\ (~ (~ (x1 = (real_of_num (NUMERAL 0))))).
Definition term204 (x0 : real) (x1 : real) := real_lt (real_mul (real_mul x0 (real_inv x1)) x1).
Definition term139 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term113 (x0 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term63 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1.
Definition term75 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term69 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term172 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ (~ (x1 = (real_of_num (NUMERAL 0))))).
Definition term91 (x0 : real) (x1 : real) := and ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))).
Definition term191 (x0 : real) (x1 : real) := real_lt (real_mul (real_inv x1) (real_mul x0 x1)).
Definition term58 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1))).
Definition term171 (x0 : real) (x1 : real) := ((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> ~ (x1 = (real_of_num (NUMERAL 0))).
Definition term97 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term72 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term218 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt y0 y1)) -> real_lt (real_inv y1) (real_inv y0).
Definition term47 := forall y0 : real, forall y1 : real, (exists y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1.
Definition term36 (x0 : real) := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul x0 y1) (real_mul y0 y1))) -> real_lt x0 y0.
Definition term34 := forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1.
Definition term25 := forall y0 : real, forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1).
Definition term13 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term12 := forall y0 : real, forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term9 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term8 (x0 : real) := forall y0 : real, forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term201 (x0 : real) (x1 : real) := real_mul (real_mul (real_inv x0) x1).
Definition term18 (x0 : real) := (fun y0 : real => (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term70 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term188 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0)) x2.
Definition term159 (x0 : real) (x1 : real) := ((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) /\ (x1 = (real_of_num (NUMERAL 0))).
Definition term41 (x0 : real) (x1 : real) (x2 : real) := (real_lt (real_of_num (NUMERAL 0)) x2) /\ (real_lt (real_mul x0 x2) (real_mul x1 x2)).
Definition term59 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1))).
Definition term99 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term42 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1) -> real_lt x0 x1.
Definition term81 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term102 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term103 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term27 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) y0)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term19 (x0 : real) := (~ (x0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term20 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term5 (x0 : real) (x1 : real) := forall y0 : real, (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term176 (x0 : real) (x1 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term71 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term78 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term92 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) \/ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0)))).
Definition term185 (x0 : real) := (fun y0 : real => (real_mul (real_of_num (NUMERAL (BIT1 0))) y0) = y0) x0.
Definition term3 (x0 : real) (x1 : real) := fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0)).
Definition term55 (x0 : real) (x1 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term7 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1)).
Definition term118 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term111 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term126 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term73 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term46 (x0 : real) := forall y0 : real, (exists y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul x0 y1) (real_mul y0 y1))) -> real_lt x0 y0.
Definition term178 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term135 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term82 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term213 (x0 : real) (x1 : real) := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul (real_inv x0) y0) (real_mul (real_inv x1) y0)).
Definition term43 (x0 : real) (x1 : real) := exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul x0 y0) (real_mul x1 y0)).
Definition term4 (x0 : real) (x1 : real) := forall y0 : real, (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term193 (x0 : real) (x1 : real) := real_mul (real_inv x0) (real_mul x0 x1).
Definition term77 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term125 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term217 (x0 : real) := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt x0 y0)) -> real_lt (real_inv y0) (real_inv x0).
Definition term174 (x0 : real) (x1 : real) := ~ (((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> ~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term160 (x0 : real) (x1 : real) := ~ (((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> ~ (x1 = (real_of_num (NUMERAL 0)))).
Definition term60 (x0 : real) (x1 : real) := ~ (((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term109 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term89 (x0 : real) := or (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term151 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term212 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1)) /\ (real_lt (real_mul (real_inv x1) (real_mul x0 x1)) (real_mul (real_inv x0) (real_mul x0 x1))).
Definition term100 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term88 (x0 : real) := or (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term146 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term6 (x0 : real) := fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1).
Definition term203 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv x1)) x1.
Definition term56 (x0 : real) (x1 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) \/ (~ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term104 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term133 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0))).
Definition term49 (x0 : real) := (fun y0 : real => forall y1 : real, (exists y2 : real, (real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1) x0.
Definition term26 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_of_num (NUMERAL 0)) y1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 y1) = (real_mul y1 y0)) x0.
Definition term95 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term98 := S (Nat.add 0 0).
Definition term116 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term29 (x0 : real) (x1 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term117 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term40 (x0 : real) (x1 : real) (x2 : real) := ((real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_mul x1 x0) (real_mul x2 x0))) -> real_lt x1 x2.
Definition term173 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (x1 = (real_of_num (NUMERAL 0))).
Definition term30 (x0 : real) (x1 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term45 (x0 : real) (x1 : real) := (exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul x0 y0) (real_mul x1 y0))) -> real_lt x0 x1.
Definition term31 (x0 : real) (x1 : real) := real_lt (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term24 := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term57 (x0 : real) (x1 : real) := and ((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)).
Definition term197 (x0 : real) (x1 : real) := real_lt (real_mul (real_inv x1) (real_mul x0 x1)) (real_mul (real_inv x0) (real_mul x0 x1)).
Definition term132 (x0 : real) (x1 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term131 (x0 : real) (x1 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term121 := real_mul (real_of_num (NUMERAL 0)).
Definition term141 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term110 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term209 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_mul x0 y0) y1) = (real_mul x0 (real_mul y0 y1))) x1.
Definition term187 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, (real_mul x0 (real_mul y0 y1)) = (real_mul (real_mul x0 y0) y1)) x1.
Definition term37 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul x0 y1) (real_mul y0 y1))) -> real_lt x0 y0) x1.
Definition term64 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term215 (x0 : real) (x1 : real) := real_lt (real_inv x0) (real_inv x1).
Definition term53 (x0 : real) (x1 : real) := (exists y0 : real, (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul (real_inv x0) y0) (real_mul (real_inv x1) y0))) -> real_lt (real_inv x0) (real_inv x1).
Definition term83 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term202 (x0 : real) (x1 : real) := real_mul (real_mul x0 (real_inv x1)).
Definition term196 := real_mul (real_of_num (NUMERAL (BIT1 0))).
Definition term52 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term195 (x0 : real) := real_mul (real_mul (real_inv x0) x0).
Definition term23 (x0 : real) := (forall y0 : real, (~ (y0 = (real_of_num (NUMERAL 0)))) -> (real_mul (real_inv y0) y0) = (real_of_num (NUMERAL (BIT1 0)))) -> (real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0))).
Definition term61 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1) (real_of_num (NUMERAL 0)).
Definition term166 (x0 : real) := ((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) = (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term123 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term84 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term182 (x0 : real) (x1 : real) := (~ (((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> ~ (x1 = (real_of_num (NUMERAL 0))))) -> False.
Definition term169 (x0 : real) (x1 : real) := (~ (((real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1)) -> ~ (x1 = (real_of_num (NUMERAL 0))))) -> False.
Definition term11 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2)).
Definition term10 := fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2).
Definition term156 (x0 : real) (x1 : real) := ((real_mul (real_inv x0) x0) = (real_of_num (NUMERAL (BIT1 0)))) /\ ((real_mul (real_inv x1) x1) = (real_of_num (NUMERAL (BIT1 0)))).
Definition term50 (x0 : real) (x1 : real) := (fun y0 : real => (exists y1 : real, (real_lt (real_of_num (NUMERAL 0)) y1) /\ (real_lt (real_mul x0 y1) (real_mul y0 y1))) -> real_lt x0 y0) x1.
Definition term86 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term39 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul x0 y0) (real_mul x1 y0))) -> real_lt x0 x1) x2.
Definition term205 (x0 : real) (x1 : real) := real_lt (real_mul (real_mul x0 (real_inv x1)) x1) x1.
Definition term214 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul (real_inv x0) y0) (real_mul (real_inv x1) y0)).
Definition term210 (x0 : real) (x1 : real) (x2 : real) := (fun y0 : real => (real_mul (real_mul x0 x1) y0) = (real_mul x0 (real_mul x1 y0))) x2.
Definition term22 := real_of_num (NUMERAL (BIT1 0)).
Definition term138 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term114 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term1 (x0 : real) (x1 : real) (x2 : real) := real_mul (real_mul x0 x1) x2.
Definition term44 (x0 : real) (x1 : real) := fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) y0) /\ (real_lt (real_mul x0 y0) (real_mul x1 y0)).
Definition term122 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term140 (x0 : real) (x1 : real) := real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term152 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term150 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term207 (x0 : real) := real_mul x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term80 (x0 : real) (x1 : real) := (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0))).
Definition term2 (x0 : real) (x1 : real) := fun y0 : real => (real_mul x0 (real_mul x1 y0)) = (real_mul (real_mul x0 x1) y0).
Definition term21 (x0 : real) := real_mul (real_inv x0) x0.
Definition term101 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term200 (x0 : real) (x1 : real) := real_mul x0 (real_inv x1).
Definition term147 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term163 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term179 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1).
Definition term142 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term137 (x0 : real) (x1 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_add x1 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)).
Definition term62 (x0 : real) (x1 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1).
Definition term206 (x0 : real) := (fun y0 : real => (real_mul y0 (real_of_num (NUMERAL (BIT1 0)))) = y0) x0.
Definition term119 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term143 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term65 (x0 : real) (x1 : real) := real_gt (real_sub x0 x1).
Definition term208 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul (real_mul y0 y1) y2) = (real_mul y0 (real_mul y1 y2))) x0.
Definition term186 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, (real_mul y0 (real_mul y1 y2)) = (real_mul (real_mul y0 y1) y2)) x0.
Definition term35 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : real, ((real_lt (real_of_num (NUMERAL 0)) y2) /\ (real_lt (real_mul y0 y2) (real_mul y1 y2))) -> real_lt y0 y1) x0.
Definition term177 (x0 : real) (x1 : real) := (((real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) = (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term144 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term134 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1)) (real_of_num (NUMERAL 0)).
Definition term129 (x0 : real) (x1 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)) (real_of_num (NUMERAL 0)).
Definition term175 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) /\ (x1 = (real_of_num (NUMERAL 0))).
Definition term162 (x0 : real) (x1 : real) := ((real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) /\ (x1 = (real_of_num (NUMERAL 0))).
Definition term54 (x0 : real) (x1 : real) := (real_lt x1 x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term181 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x1) (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1)).
Definition term68 (x0 : real) (x1 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0)).
Definition term154 (x0 : real) (x1 : real) := ((~ (((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1))) -> False) -> ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term157 (x0 : real) := ~ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term105 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term74 := NUMERAL (BIT1 0).
Definition term155 (x0 : real) (x1 : real) := ((real_lt x0 x1) /\ (real_lt (real_of_num (NUMERAL 0)) x0)) -> (real_lt (real_of_num (NUMERAL 0)) x0) /\ (real_lt (real_of_num (NUMERAL 0)) x1).
Definition term167 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term148 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term112 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term106 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term115 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term96 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term199 (x0 : real) (x1 : real) := real_mul (real_inv x0) x1.
Definition term128 (x0 : real) (x1 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x1) (real_of_num (NUMERAL 0))).
Definition term124 := real_gt (real_of_num (NUMERAL 0)).
