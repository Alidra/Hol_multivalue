Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0))) x1.
Definition term30 (x0 : real) := real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term42 (x0 : real) := @COND real True (real_mul x0 x0) (real_neg (real_mul x0 x0)).
Definition term18 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_abs y0)) x0.
Definition term19 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_abs x0).
Definition term37 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)) (real_mul x0 x0) (real_neg (real_mul x0 x0)).
Definition term36 (x0 : real) := True /\ ((real_abs (real_mul x0 x0)) = (real_mul x0 x0)).
Definition term27 := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1.
Definition term6 (x0 : real) := fun y0 : real => (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term29 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) (real_abs x0)).
Definition term16 (x0 : real) := (fun y0 : real => (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_mul y0 y0)) x0.
Definition term45 := forall y0 : real, (sqrt (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))) = (real_abs y0).
Definition term20 := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1.
Definition term13 := forall y0 : real, forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1)).
Definition term12 := forall y0 : real, forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1)).
Definition term23 (x0 : real) (x1 : real) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = y0) x1.
Definition term25 (x0 : real) (x1 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = x1).
Definition term43 (x0 : real) := @eq real (real_mul x0 x0).
Definition term28 (x0 : real) := ((real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))))) -> (sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) = (real_abs x0).
Definition term1 (x0 : real) := real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0).
Definition term10 := fun y0 : real => forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1)).
Definition term32 (x0 : real) := real_abs (real_mul x0 x0).
Definition term35 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) (real_abs x0)) /\ ((real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term17 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term40 (x0 : real) := @COND real True (real_mul x0 x0).
Definition term33 (x0 : real) := @eq real (real_pow (real_abs x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term4 (x0 : real) (x1 : real) := real_abs (real_mul x0 x1).
Definition term44 (x0 : real) := sqrt (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term21 (x0 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1))) x0.
Definition term7 (x0 : real) := fun y0 : real => (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0)).
Definition term2 (x0 : real) := (fun y0 : real => (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))) x0.
Definition term22 (x0 : real) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = y0.
Definition term0 (x0 : real) := (fun y0 : real => real_le (real_of_num (NUMERAL 0)) (real_mul y0 y0)) x0.
Definition term3 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0).
Definition term41 (x0 : real) := real_neg (real_mul x0 x0).
Definition term31 (x0 : real) := real_mul (real_abs x0) (real_abs x0).
Definition term9 (x0 : real) := forall y0 : real, (real_mul (real_abs x0) (real_abs y0)) = (real_abs (real_mul x0 y0)).
Definition term39 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)) (real_mul x0 x0).
Definition term34 (x0 : real) := @eq real (real_abs (real_mul x0 x0)).
Definition term8 (x0 : real) := forall y0 : real, (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term38 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_mul x0 x0)).
Definition term5 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs x1).
Definition term24 (x0 : real) (x1 : real) := ((real_le (real_of_num (NUMERAL 0)) x1) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = x0)) -> (sqrt x0) = x1.
Definition term26 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = y0)) -> (sqrt y0) = y1) -> (sqrt x0) = x1.
Definition term11 := fun y0 : real => forall y1 : real, (real_mul (real_abs y0) (real_abs y1)) = (real_abs (real_mul y0 y1)).
