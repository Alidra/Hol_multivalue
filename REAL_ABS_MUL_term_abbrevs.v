Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0))) x1.
Definition term38 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term7 (x0 : real) := real_neg (real_neg x0).
Definition term68 (x0 : real) (x1 : real) := @COND real True (real_mul x0 x1) (real_neg (real_mul x0 x1)).
Definition term75 (x0 : real) (x1 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg (real_mul x0 x1))) (real_neg (real_mul x0 x1)).
Definition term22 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term10 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0))) x1.
Definition term25 (x0 : real) := real_mul (real_abs x0).
Definition term84 (x0 : real) := real_mul (real_neg x0).
Definition term39 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) x1).
Definition term83 (x0 : real) := @COND real True (real_neg x0) x0.
Definition term60 (x0 : real) (x1 : real) := real_abs (real_neg (real_mul x0 x1)).
Definition term70 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0).
Definition term59 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) -> (real_abs (real_mul x0 x1)) = (real_mul (real_abs (real_neg x0)) (real_abs (real_neg x1))).
Definition term71 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0.
Definition term33 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1).
Definition term24 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg x0).
Definition term35 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_neg x1)).
Definition term53 (x0 : real) (x1 : real) := real_mul (real_neg x0) (real_neg x1).
Definition term42 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_neg x1))) -> real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x1)).
Definition term43 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x1)).
Definition term11 (x0 : real) (x1 : real) := real_mul x0 (real_neg x1).
Definition term48 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_neg x1))) -> (real_abs (real_mul x0 x1)) = (real_mul (real_abs x0) (real_abs (real_neg x1))).
Definition term55 (x0 : real) (x1 : real) := real_neg (real_neg (real_mul x0 x1)).
Definition term2 := fun y0 : real => (real_abs y0) = (real_abs (real_neg y0)).
Definition term3 := forall y0 : real, (real_abs (real_neg y0)) = (real_abs y0).
Definition term64 (x0 : real) (x1 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) (real_mul x0 x1) (real_neg (real_mul x0 x1)).
Definition term31 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs (real_neg x1)).
Definition term87 := forall y0 : real, forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1)).
Definition term85 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) -> (real_abs (real_mul x0 x1)) = (real_mul (real_abs x0) (real_abs x1)).
Definition term5 (x0 : real) := (fun y0 : real => (real_abs y0) = (real_abs (real_neg y0))) x0.
Definition term36 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) (real_neg x1))) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_neg x1)).
Definition term44 := real_le (real_of_num (NUMERAL 0)).
Definition term18 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0).
Definition term12 (x0 : real) (x1 : real) := real_neg (real_mul x0 x1).
Definition term51 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) x1)) -> (real_abs (real_mul x0 x1)) = (real_mul (real_abs (real_neg x0)) (real_abs x1)).
Definition term76 (x0 : real) (x1 : real) := @COND real True (real_neg (real_mul x0 x1)).
Definition term46 (x0 : real) (x1 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_neg x1))).
Definition term19 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) y0)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 y0)) x1.
Definition term65 (x0 : real) (x1 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)).
Definition term40 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) x1).
Definition term30 (x0 : real) (x1 : real) := real_abs (real_mul x0 x1).
Definition term54 (x0 : real) (x1 : real) := real_neg (real_mul x0 (real_neg x1)).
Definition term6 (x0 : real) := (fun y0 : real => (real_neg (real_neg y0)) = y0) x0.
Definition term9 (x0 : real) := forall y0 : real, (real_mul x0 (real_neg y0)) = (real_neg (real_mul x0 y0)).
Definition term17 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le (real_of_num (NUMERAL 0)) y1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul y0 y1)) x0.
Definition term13 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_neg y0) y1) = (real_neg (real_mul y0 y1))) x0.
Definition term8 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul y0 (real_neg y1)) = (real_neg (real_mul y0 y1))) x0.
Definition term81 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) (real_neg x0).
Definition term34 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term16 (x0 : real) (x1 : real) := real_mul (real_neg x0) x1.
Definition term23 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term62 (x0 : real) := (fun y0 : real => (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))) x0.
Definition term63 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0).
Definition term26 (x0 : real) := real_mul (real_abs (real_neg x0)).
Definition term77 (x0 : real) (x1 : real) := @COND real True (real_neg (real_mul x0 x1)) (real_mul x0 x1).
Definition term49 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg (real_mul x0 x1))) -> (real_abs (real_mul x0 x1)) = (real_mul (real_abs x0) (real_abs (real_neg x1))).
Definition term73 (x0 : real) (x1 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg (real_mul x0 x1))) (real_neg (real_mul x0 x1)) (real_neg (real_neg (real_mul x0 x1))).
Definition term14 (x0 : real) := forall y0 : real, (real_mul (real_neg x0) y0) = (real_neg (real_mul x0 y0)).
Definition term47 (x0 : real) (x1 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_neg (real_mul x0 x1))).
Definition term67 (x0 : real) (x1 : real) := @COND real True (real_mul x0 x1).
Definition term28 (x0 : real) (x1 : real) := real_mul (real_abs (real_neg x0)) (real_abs x1).
Definition term21 (x0 : real) := (fun y0 : real => (real_le (real_of_num (NUMERAL 0)) y0) \/ (real_le (real_of_num (NUMERAL 0)) (real_neg y0))) x0.
Definition term4 := forall y0 : real, (real_abs y0) = (real_abs (real_neg y0)).
Definition term69 (x0 : real) (x1 : real) := @eq real (real_mul x0 x1).
Definition term86 (x0 : real) := forall y0 : real, (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term45 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_neg (real_mul x0 x1)).
Definition term56 (x0 : real) (x1 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x1))).
Definition term58 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) (real_neg x1))) -> (real_abs (real_mul x0 x1)) = (real_mul (real_abs (real_neg x0)) (real_abs (real_neg x1))).
Definition term20 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le (real_of_num (NUMERAL 0)) x1)) -> real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1).
Definition term27 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs x1).
Definition term79 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) (real_neg x0) (real_neg (real_neg x0)).
Definition term50 (x0 : real) (x1 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_mul (real_neg x0) x1)).
Definition term61 (x0 : real) (x1 : real) := @eq real (real_abs (real_neg (real_mul x0 x1))).
Definition term29 (x0 : real) (x1 : real) := @eq real (real_abs (real_mul x0 x1)).
Definition term0 (x0 : real) := real_abs (real_neg x0).
Definition term1 := fun y0 : real => (real_abs (real_neg y0)) = (real_abs y0).
Definition term80 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg x0)).
Definition term37 (x0 : real) (x1 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 (real_neg x1)).
Definition term52 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg (real_mul x0 x1))) -> (real_abs (real_mul x0 x1)) = (real_mul (real_abs (real_neg x0)) (real_abs x1)).
Definition term57 (x0 : real) (x1 : real) := imp (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)).
Definition term41 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) (real_neg x0)) /\ (real_le (real_of_num (NUMERAL 0)) (real_neg x1)).
Definition term74 (x0 : real) (x1 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_neg (real_mul x0 x1))).
Definition term32 (x0 : real) (x1 : real) := real_mul (real_abs (real_neg x0)) (real_abs (real_neg x1)).
Definition term82 (x0 : real) := @COND real True (real_neg x0).
Definition term66 (x0 : real) (x1 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x1)) (real_mul x0 x1).
Definition term72 (x0 : real) := @COND real True x0 (real_neg x0).
Definition term78 (x0 : real) (x1 : real) := @eq real (real_neg (real_mul x0 x1)).
