Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term100 := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))).
Definition term128 (x0 : real) := @eq real (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term123 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term117 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term87 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term32 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term114 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term108 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term1 := real_of_num (NUMERAL 0).
Definition term127 (x0 : real) := (fun y0 : real => (real_mul y0 x0) = (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL (BIT1 0))).
Definition term62 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term146 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term126 (x0 : real) := forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term72 (x0 : real) := (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ (((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))))).
Definition term49 (x0 : real) := and (~ (real_lt (real_of_num (NUMERAL 0)) x0)).
Definition term136 (x0 : real) := @eq Prop (real_le (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term47 (x0 : real) := or (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term144 := fun y0 : real => True.
Definition term132 (x0 : real) := (~ ((real_le (real_of_num (NUMERAL 0)) x0) = ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))))) -> False.
Definition term110 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term34 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term139 := fun y0 : real => ((real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) \/ ((sqrt y0) = (real_of_num (NUMERAL 0)))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term137 (x0 : real) := @eq Prop ((real_lt (real_of_num (NUMERAL 0)) (sqrt x0)) \/ ((sqrt x0) = (real_of_num (NUMERAL 0)))).
Definition term58 (x0 : real) := or (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term55 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term57 (x0 : real) := @eq real (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term71 (x0 : real) := or (((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term26 (x0 : real) := real_ge x0 (real_of_num (NUMERAL 0)).
Definition term70 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term43 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term145 := forall y0 : real, True.
Definition term131 (x0 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term93 (x0 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term147 (x0 : Prop) := forall y0 : real, x0.
Definition term52 (x0 : real) := and (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term24 (x0 : real) := real_add x0 (real_of_num (NUMERAL 0)).
Definition term44 (x0 : real) := real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term64 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))))).
Definition term60 (x0 : real) := and (~ (real_le (real_of_num (NUMERAL 0)) x0)).
Definition term54 (x0 : real) := ~ (real_le (real_of_num (NUMERAL 0)) x0).
Definition term76 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term56 (x0 : real) := real_gt (real_sub (real_of_num (NUMERAL 0)) x0).
Definition term21 (x0 : nat) := real_mul (real_neg (real_of_num x0)) (real_of_num (NUMERAL 0)).
Definition term59 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term19 (x0 : real) := real_sub x0 (real_of_num (NUMERAL 0)).
Definition term50 (x0 : real) := and (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term14 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ (x0 = (real_of_num (NUMERAL 0)))))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0))))).
Definition term41 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0)).
Definition term78 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term27 (x0 : real) := ~ (real_lt (real_of_num (NUMERAL 0)) x0).
Definition term82 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term83 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term35 (x0 : real) := ~ (x0 = (real_of_num (NUMERAL 0))).
Definition term66 (x0 : real) := ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term20 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0))).
Definition term133 (x0 : real) := ((~ ((real_le (real_of_num (NUMERAL 0)) x0) = ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))))) -> False) -> (real_le (real_of_num (NUMERAL 0)) x0) = ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term8 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term46 (x0 : real) := or (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))).
Definition term138 := fun y0 : real => (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term2 (x0 : real) := (fun y0 : real => (real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) = (real_lt (real_of_num (NUMERAL 0)) y0)) x0.
Definition term63 (x0 : real) := or ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))))).
Definition term98 (x0 : nat) := real_add (real_neg (real_of_num x0)) (real_of_num x0).
Definition term12 (x0 : real) := or ((real_le (real_of_num (NUMERAL 0)) x0) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ (x0 = (real_of_num (NUMERAL 0)))))).
Definition term91 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term36 (x0 : real) := (real_gt (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0))) \/ (real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))) (real_of_num (NUMERAL 0))).
Definition term106 := Peano.lt (NUMERAL 0) (NUMERAL 0).
Definition term22 := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL 0)).
Definition term38 (x0 : real) := @eq real (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term51 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term28 (x0 : real) := real_ge (real_sub (real_of_num (NUMERAL 0)) x0) (real_of_num (NUMERAL 0)).
Definition term140 := forall y0 : real, (real_le (real_of_num (NUMERAL 0)) (sqrt y0)) = (real_le (real_of_num (NUMERAL 0)) y0).
Definition term134 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term17 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0))).
Definition term141 := forall y0 : real, ((real_lt (real_of_num (NUMERAL 0)) (sqrt y0)) \/ ((sqrt y0) = (real_of_num (NUMERAL 0)))) = ((real_lt (real_of_num (NUMERAL 0)) y0) \/ (y0 = (real_of_num (NUMERAL 0)))).
Definition term45 (x0 : real) := real_gt x0 (real_of_num (NUMERAL 0)).
Definition term65 (x0 : real) := ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ ((real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0)))).
Definition term105 := real_gt (real_of_num (NUMERAL 0)) (real_of_num (NUMERAL 0)).
Definition term13 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))))) \/ ((~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0))))).
Definition term109 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term89 (x0 : real) := real_mul (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term10 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ (x0 = (real_of_num (NUMERAL 0))))).
Definition term119 (x0 : real) := real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0.
Definition term79 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_ge (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term115 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term39 (x0 : real) := real_gt (real_neg (real_sub x0 (real_of_num (NUMERAL 0)))).
Definition term6 (x0 : real) := (~ (real_lt (real_of_num (NUMERAL 0)) x0)) /\ (~ (x0 = (real_of_num (NUMERAL 0)))).
Definition term84 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term74 (x0 : nat) (x1 : nat) := real_gt (real_of_num x0) (real_of_num x1).
Definition term77 := S (Nat.add 0 0).
Definition term96 (x0 : real) := real_mul (real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term16 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term97 := real_neg (real_of_num (NUMERAL (BIT1 0))).
Definition term11 (x0 : real) := or ((real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))))).
Definition term61 (x0 : real) := and (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term101 := real_mul (real_of_num (NUMERAL 0)).
Definition term90 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term40 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term31 (x0 : real) := real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term29 (x0 : real) := real_sub (real_of_num (NUMERAL 0)) x0.
Definition term48 (x0 : real) := (real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term135 (x0 : real) := (real_lt (real_of_num (NUMERAL 0)) (sqrt x0)) \/ ((sqrt x0) = (real_of_num (NUMERAL 0))).
Definition term69 (x0 : real) := (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term4 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) x0.
Definition term103 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)).
Definition term30 (x0 : real) := real_add (real_of_num (NUMERAL 0)) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term67 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ (((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))) \/ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term7 (x0 : real) := (~ (real_le (real_of_num (NUMERAL 0)) x0)) /\ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term111 (x0 : real) := real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) x0).
Definition term33 (x0 : real) := real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term5 (x0 : real) := ~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term15 (x0 : real) := ~ ((real_le (real_of_num (NUMERAL 0)) x0) = ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0))))).
Definition term68 (x0 : real) := ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))))) \/ ((real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term81 := real_of_num (NUMERAL (BIT1 0)).
Definition term94 (x0 : real) := real_gt (real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term37 (x0 : real) := real_neg (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term102 (x0 : real) := real_mul (real_of_num (NUMERAL 0)) x0.
Definition term120 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0).
Definition term9 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (~ ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0))))).
Definition term118 (x0 : real) := real_gt (real_add (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) x0) (real_of_num (NUMERAL 0)).
Definition term129 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term73 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0)))).
Definition term80 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_ge (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term124 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (x0 = (real_of_num (NUMERAL 0))).
Definition term121 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term125 (x0 : real) := (x0 = (real_of_num (NUMERAL 0))) -> forall y0 : real, (real_mul y0 x0) = (real_of_num (NUMERAL 0)).
Definition term116 (x0 : real) := (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_ge x0 (real_of_num (NUMERAL 0))).
Definition term88 (x0 : real) := real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) x0) (real_of_num (NUMERAL 0)).
Definition term42 (x0 : real) := real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)).
Definition term3 (x0 : real) := real_lt (real_of_num (NUMERAL 0)) (sqrt x0).
Definition term99 := real_add (real_neg (real_of_num (NUMERAL (BIT1 0)))) (real_of_num (NUMERAL (BIT1 0))).
Definition term107 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))).
Definition term0 (x0 : real) := (fun y0 : real => ((sqrt y0) = (real_of_num (NUMERAL 0))) = (y0 = (real_of_num (NUMERAL 0)))) x0.
Definition term53 (x0 : real) := (real_ge x0 (real_of_num (NUMERAL 0))) /\ ((real_ge (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))) /\ ((real_gt x0 (real_of_num (NUMERAL 0))) \/ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))))).
Definition term112 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0))).
Definition term25 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))).
Definition term142 (x0 : real) := or (real_lt (real_of_num (NUMERAL 0)) (sqrt x0)).
Definition term18 (x0 : real) := real_ge (real_sub x0 (real_of_num (NUMERAL 0))) (real_of_num (NUMERAL 0)).
Definition term113 (x0 : real) := ((real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0) (real_of_num (NUMERAL 0)))) -> real_gt (real_mul (real_of_num (NUMERAL (BIT1 0))) (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0)) (real_of_num (NUMERAL 0)).
Definition term85 (x0 : real) := (real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0))) /\ (real_gt x0 (real_of_num (NUMERAL 0))).
Definition term23 := NUMERAL (BIT1 0).
Definition term143 (x0 : real) := @eq Prop ((real_lt (real_of_num (NUMERAL 0)) x0) \/ (x0 = (real_of_num (NUMERAL 0)))).
Definition term130 (x0 : real) (x1 : real) := ((x0 = (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term122 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term92 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_ge x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_add x0 x1) (real_of_num (NUMERAL 0)).
Definition term86 (x0 : real) (x1 : real) := ((real_gt x0 (real_of_num (NUMERAL 0))) /\ (real_gt x1 (real_of_num (NUMERAL 0)))) -> real_gt (real_mul x0 x1) (real_of_num (NUMERAL 0)).
Definition term95 (x0 : real) := real_add x0 (real_mul (real_neg (real_of_num (NUMERAL (BIT1 0)))) x0).
Definition term75 := real_gt (real_of_num (NUMERAL (BIT1 0))) (real_of_num (NUMERAL 0)).
Definition term104 := real_gt (real_of_num (NUMERAL 0)).