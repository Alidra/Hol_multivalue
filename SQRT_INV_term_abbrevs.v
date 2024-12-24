Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term19 := (forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) -> forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1.
Definition term16 (x0 : real) (x1 : real) := (((real_sgn x1) = (real_sgn x0)) /\ ((real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = x1.
Definition term12 := forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1.
Definition term35 := forall y0 : real, (sqrt (real_inv y0)) = (real_inv (sqrt y0)).
Definition term34 (x0 : real) := sqrt (real_inv x0).
Definition term4 (x0 : real) := real_inv (real_abs x0).
Definition term27 (x0 : real) := real_pow (real_inv (sqrt x0)) (NUMERAL (BIT0 (BIT1 0))).
Definition term1 (x0 : real) := ((real_sgn (sqrt x0)) = (real_sgn x0)) /\ ((real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0)).
Definition term5 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_inv y0) y1) = (real_inv (real_pow y0 y1))) x0.
Definition term26 (x0 : real) := and ((real_sgn (real_inv (sqrt x0))) = (real_sgn (real_inv x0))).
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => (((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = y0) x1.
Definition term7 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0))) x1.
Definition term20 (x0 : real) := (((real_sgn (real_inv (sqrt x0))) = (real_sgn (real_inv x0))) /\ ((real_pow (real_inv (sqrt x0)) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs (real_inv x0)))) -> (sqrt (real_inv x0)) = (real_inv (sqrt x0)).
Definition term0 (x0 : real) := (fun y0 : real => ((real_sgn (sqrt y0)) = (real_sgn y0)) /\ ((real_pow (sqrt y0) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) x0.
Definition term13 (x0 : real) := (fun y0 : real => forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) x0.
Definition term2 (x0 : real) := (fun y0 : real => (real_abs (real_inv y0)) = (real_inv (real_abs y0))) x0.
Definition term21 (x0 : real) := real_inv (sqrt x0).
Definition term3 (x0 : real) := real_abs (real_inv x0).
Definition term14 (x0 : real) := forall y0 : real, (((real_sgn y0) = (real_sgn x0)) /\ ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x0))) -> (sqrt x0) = y0.
Definition term25 (x0 : real) := @eq real (real_sgn x0).
Definition term6 (x0 : real) := forall y0 : nat, (real_pow (real_inv x0) y0) = (real_inv (real_pow x0 y0)).
Definition term29 := NUMERAL (BIT0 (BIT1 0)).
Definition term32 (x0 : real) := @eq real (real_inv (real_abs x0)).
Definition term23 (x0 : real) := real_sgn (sqrt x0).
Definition term30 (x0 : real) := real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0))).
Definition term8 (x0 : real) (x1 : nat) := real_pow (real_inv x0) x1.
Definition term9 (x0 : real) (x1 : nat) := real_inv (real_pow x0 x1).
Definition term10 (x0 : real) := (fun y0 : real => (real_sgn (real_inv y0)) = (real_sgn y0)) x0.
Definition term22 (x0 : real) := real_sgn (real_inv (sqrt x0)).
Definition term11 (x0 : real) := real_sgn (real_inv x0).
Definition term17 (x0 : real) (x1 : real) := ((real_sgn x0) = (real_sgn x1)) /\ ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs x1)).
Definition term31 (x0 : real) := @eq real (real_pow (real_inv (sqrt x0)) (NUMERAL (BIT0 (BIT1 0)))).
Definition term33 (x0 : real) := ((real_sgn (real_inv (sqrt x0))) = (real_sgn (real_inv x0))) /\ ((real_pow (real_inv (sqrt x0)) (NUMERAL (BIT0 (BIT1 0)))) = (real_abs (real_inv x0))).
Definition term18 (x0 : real) (x1 : real) := (forall y0 : real, forall y1 : real, (((real_sgn y1) = (real_sgn y0)) /\ ((real_pow y1 (NUMERAL (BIT0 (BIT1 0)))) = (real_abs y0))) -> (sqrt y0) = y1) -> (sqrt x0) = x1.
Definition term24 (x0 : real) := @eq real (real_sgn (real_inv (sqrt x0))).
Definition term28 (x0 : real) := real_inv (real_pow (sqrt x0) (NUMERAL (BIT0 (BIT1 0)))).
