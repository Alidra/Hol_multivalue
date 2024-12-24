Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term2 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term11 (x0 : real) (x1 : real) := (fun y0 : real => (real_le (real_abs x0) (real_abs y0)) = (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))))) x1.
Definition term18 (x0 : real) (x1 : real) := and (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term27 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term24 := fun y0 : real => True.
Definition term12 (x0 : real) (x1 : real) := real_le (real_abs x0) (real_abs x1).
Definition term15 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term26 := forall y0 : real, True.
Definition term28 (x0 : Prop) := forall y0 : real, x0.
Definition term30 := forall y0 : real, forall y1 : real, ((real_abs y0) = (real_abs y1)) = ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term8 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term7 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term21 (x0 : real) (x1 : real) := @eq Prop ((real_le (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))))).
Definition term19 (x0 : real) (x1 : real) := (real_le (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x0 (NUMERAL (BIT0 (BIT1 0))))) /\ (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term29 := fun y0 : real => forall y1 : real, ((real_abs y0) = (real_abs y1)) = ((real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y1 (NUMERAL (BIT0 (BIT1 0))))).
Definition term6 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term0 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term22 (x0 : real) := real_pow x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term25 (x0 : real) := forall y0 : real, ((real_abs x0) = (real_abs y0)) = ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term10 (x0 : real) := forall y0 : real, (real_le (real_abs x0) (real_abs y0)) = (real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term5 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term14 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term9 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le (real_abs y0) (real_abs y1)) = (real_le (real_pow y0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow y1 (NUMERAL (BIT0 (BIT1 0)))))) x0.
Definition term17 (x0 : real) (x1 : real) := and (real_le (real_abs x0) (real_abs x1)).
Definition term16 (x0 : real) (x1 : real) := (real_le (real_abs x1) (real_abs x0)) /\ (real_le (real_abs x0) (real_abs x1)).
Definition term1 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term13 (x0 : real) (x1 : real) := real_le (real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) (real_pow x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term23 (x0 : real) := fun y0 : real => ((real_abs x0) = (real_abs y0)) = ((real_pow x0 (NUMERAL (BIT0 (BIT1 0)))) = (real_pow y0 (NUMERAL (BIT0 (BIT1 0))))).
Definition term4 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term20 (x0 : real) (x1 : real) := @eq Prop ((real_abs x0) = (real_abs x1)).
