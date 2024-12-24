Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : real) (x1 : real) := (((real_sgn (real_mul (sqrt x0) (sqrt x1))) = (real_sgn (real_mul x0 x1))) /\ ((real_pow (real_mul (sqrt x0) (sqrt x1)) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs (real_mul x0 x1)))) -> (sqrt (real_mul x0 x1)) = (real_mul (sqrt x0) (sqrt x1)).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0))) x1.
Definition term12 (x0 : real) (x1 : real) (x2 : nat) := real_pow (real_mul x0 x1) x2.
Definition term42 (x0 : real) := real_mul (real_abs x0).
Definition term13 (x0 : real) (x1 : real) (x2 : nat) := real_mul (real_pow x0 x2) (real_pow x1 x2).
Definition term18 (x0 : real) (x1 : real) := real_mul (real_sgn x0) (real_sgn x1).
Definition term26 := (forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) -> forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1.
Definition term23 (x0 : real) (x1 : real) := (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1.
Definition term37 (x0 : real) (x1 : real) := real_pow (real_mul (sqrt x0) (sqrt x1)) (NUMERAL (BIT0 (BIT1 0))).
Definition term41 (x0 : real) := real_mul (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))).
Definition term32 (x0 : real) := real_mul (real_sgn (sqrt x0)).
Definition term48 := forall y0 : real, forall y1 : real, (sqrt (real_mul y0 y1)) = (real_mul (sqrt y0) (sqrt y1)).
Definition term19 := forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1.
Definition term8 (x0 : real) := forall y0 : real, forall y1 : nat, (real_pow (real_mul x0 y0) y1) = (real_mul (real_pow x0 y1) (real_pow y0 y1)).
Definition term33 (x0 : real) := real_mul (real_sgn x0).
Definition term45 (x0 : real) (x1 : real) := ((real_sgn (real_mul (sqrt x0) (sqrt x1))) = (real_sgn (real_mul x0 x1))) /\ ((real_pow (real_mul (sqrt x0) (sqrt x1)) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs (real_mul x0 x1))).
Definition term6 (x0 : real) := ((real_sgn (sqrt x0)) = (real_sgn x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0)).
Definition term30 (x0 : real) (x1 : real) := real_mul (real_sgn (sqrt x0)) (real_sgn (sqrt x1)).
Definition term22 (x0 : real) (x1 : real) := (fun y0 : real => (((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = y0) x1.
Definition term43 (x0 : real) (x1 : real) := @eq real (real_pow (real_mul (sqrt x0) (sqrt x1)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term5 (x0 : real) := (fun y0 : real => ((real_sgn (sqrt y0)) = (real_sgn y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) x0.
Definition term29 (x0 : real) (x1 : real) := real_sgn (real_mul (sqrt x0) (sqrt x1)).
Definition term3 (x0 : real) (x1 : real) := real_abs (real_mul x0 x1).
Definition term36 (x0 : real) (x1 : real) := and ((real_sgn (real_mul (sqrt x0) (sqrt x1))) = (real_sgn (real_mul x0 x1))).
Definition term20 (x0 : real) := (fun y0 : real => forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) x0.
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, (real_sgn (real_mul y0 y1)) = (real_mul (real_sgn y0) (real_sgn y1))) x0.
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_abs (real_mul y0 y1)) = (real_mul (real_abs y0) (real_abs y1))) x0.
Definition term21 (x0 : real) := forall y0 : real, (((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = y0.
Definition term11 (x0 : real) (x1 : real) (x2 : nat) := (fun y0 : nat => (real_pow (real_mul x0 x1) y0) = (real_mul (real_pow x0 y0) (real_pow x1 y0))) x2.
Definition term39 := NUMERAL (BIT0 (BIT1 0)).
Definition term38 (x0 : real) (x1 : real) := real_mul (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) (real_pow (sqrt x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term46 (x0 : real) (x1 : real) := sqrt (real_mul x0 x1).
Definition term17 (x0 : real) (x1 : real) := real_sgn (real_mul x0 x1).
Definition term31 (x0 : real) := real_sgn (sqrt x0).
Definition term40 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term47 (x0 : real) := forall y0 : real, (sqrt (real_mul x0 y0)) = (real_mul (sqrt x0) (sqrt y0)).
Definition term15 (x0 : real) := forall y0 : real, (real_sgn (real_mul x0 y0)) = (real_mul (real_sgn x0) (real_sgn y0)).
Definition term1 (x0 : real) := forall y0 : real, (real_abs (real_mul x0 y0)) = (real_mul (real_abs x0) (real_abs y0)).
Definition term28 (x0 : real) (x1 : real) := real_mul (sqrt x0) (sqrt x1).
Definition term10 (x0 : real) (x1 : real) := forall y0 : nat, (real_pow (real_mul x0 x1) y0) = (real_mul (real_pow x0 y0) (real_pow x1 y0)).
Definition term4 (x0 : real) (x1 : real) := real_mul (real_abs x0) (real_abs x1).
Definition term16 (x0 : real) (x1 : real) := (fun y0 : real => (real_sgn (real_mul x0 y0)) = (real_mul (real_sgn x0) (real_sgn y0))) x1.
Definition term44 (x0 : real) (x1 : real) := @eq real (real_mul (real_abs x0) (real_abs x1)).
Definition term24 (x0 : real) (x1 : real) := ((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1)).
Definition term34 (x0 : real) (x1 : real) := @eq real (real_sgn (real_mul (sqrt x0) (sqrt x1))).
Definition term7 (x0 : real) := (fun y0 : real => forall y1 : real, forall y2 : nat, (real_pow (real_mul y0 y1) y2) = (real_mul (real_pow y0 y2) (real_pow y1 y2))) x0.
Definition term25 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) -> (sqrt x0) = x1.
Definition term35 (x0 : real) (x1 : real) := @eq real (real_mul (real_sgn x0) (real_sgn x1)).
Definition term9 (x0 : real) (x1 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_mul x0 y0) y1) = (real_mul (real_pow x0 y1) (real_pow y0 y1))) x1.
