Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 y2)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term11 (x0 : nat) := real_pow (real_of_num (NUMERAL (BIT1 0))) x0.
Definition term20 (x0 : real) (x1 : nat) := (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_pow x0 x1) (real_pow (real_of_num (NUMERAL (BIT1 0))) x1)) -> real_le (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term15 (x0 : real) (x1 : nat) := real_le (real_pow x0 x1) (real_pow (real_of_num (NUMERAL (BIT1 0))) x1).
Definition term1 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term3 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term12 (x0 : real) := and (real_le (real_of_num (NUMERAL 0)) x0).
Definition term23 (x0 : nat) := forall y0 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_pow y0 x0) (real_of_num (NUMERAL (BIT1 0))).
Definition term13 (x0 : real) := imp ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0))))).
Definition term21 (x0 : real) (x1 : nat) := (real_le (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0)))) -> real_le (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term8 (x0 : real) := real_le x0 (real_of_num (NUMERAL (BIT1 0))).
Definition term24 := forall y0 : nat, forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y1) /\ (real_le y1 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_pow y1 y0) (real_of_num (NUMERAL (BIT1 0))).
Definition term9 (x0 : real) := real_le (real_of_num (NUMERAL 0)) x0.
Definition term14 (x0 : real) (x1 : nat) := real_le (real_pow x0 x1).
Definition term4 (x0 : real) (x1 : nat) := (fun y0 : real => ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 y0)) -> real_le (real_pow x0 x1) (real_pow y0 x1)) (real_of_num (NUMERAL (BIT1 0))).
Definition term19 (x0 : real) (x1 : nat) := imp (real_le (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0)))).
Definition term2 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_le (real_of_num (NUMERAL 0)) y0) /\ (real_le y0 y1)) -> real_le (real_pow y0 x0) (real_pow y1 x0)) x1.
Definition term7 (x0 : real) := (real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0)))).
Definition term18 (x0 : real) (x1 : nat) := imp (((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_pow x0 x1) (real_pow (real_of_num (NUMERAL (BIT1 0))) x1)).
Definition term17 (x0 : real) (x1 : nat) := True -> real_le (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term22 (x0 : real) (x1 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0))).
Definition term5 := real_of_num (NUMERAL (BIT1 0)).
Definition term10 (x0 : nat) := (fun y0 : nat => (real_pow (real_of_num (NUMERAL (BIT1 0))) y0) = (real_of_num (NUMERAL (BIT1 0)))) x0.
Definition term6 (x0 : real) (x1 : nat) := ((real_le (real_of_num (NUMERAL 0)) x0) /\ (real_le x0 (real_of_num (NUMERAL (BIT1 0))))) -> real_le (real_pow x0 x1) (real_pow (real_of_num (NUMERAL (BIT1 0))) x1).
Definition term16 (x0 : real) (x1 : nat) := real_le (real_pow x0 x1) (real_of_num (NUMERAL (BIT1 0))).
