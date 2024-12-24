Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term17 (x0 : nat) := imp (x0 = (NUMERAL (BIT1 0))).
Definition term27 (x0 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) -> (x0 = (NUMERAL (BIT1 0))) = False.
Definition term3 (x0 : nat) := ~ (x0 = (NUMERAL (BIT1 0))).
Definition term25 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term20 (x0 : nat) (x1 : nat) := (num_divides x0 x1) -> (x0 = (NUMERAL (BIT1 0))) \/ (x0 = x1).
Definition term16 (x0 : nat) (x1 : nat) := imp (num_divides x0 x1).
Definition term18 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (x0 = x1).
Definition term30 (x0 : nat) := @eq Prop (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)).
Definition term13 (x0 : nat) := num_divides x0 (NUMERAL (BIT1 0)).
Definition term22 (x0 : nat) := fun y0 : nat => (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0).
Definition term33 (x0 : nat) := @eq Prop (((forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)) = (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0))) = True).
Definition term6 (x0 : nat) := or (x0 = (NUMERAL (BIT1 0))).
Definition term11 (x0 : nat) := forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0).
Definition term5 (x0 : nat) := (~ (x0 = (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)).
Definition term34 := forall y0 : nat, ((y0 = (NUMERAL (BIT1 0))) \/ (prime y0)) = (forall y1 : nat, (num_divides y1 y0) -> (y1 = (NUMERAL (BIT1 0))) \/ (y1 = y0)).
Definition term28 (x0 : nat) := True /\ (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)).
Definition term32 (x0 : nat) := @eq Prop ((fun y0 : Prop => y0 = True) ((forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)) = (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)))).
Definition term0 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL (BIT1 0))).
Definition term24 := forall y0 : nat, True.
Definition term10 (x0 : nat) := @eq Prop ((x0 = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)))).
Definition term15 (x0 : nat) := and (~ (x0 = (NUMERAL (BIT1 0)))).
Definition term23 := fun y0 : nat => True.
Definition term29 (x0 : nat) := False \/ (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)).
Definition term19 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (x0 = (NUMERAL (BIT1 0))).
Definition term4 (x0 : nat) := (fun y0 : nat => (prime y0) = ((~ (y0 = (NUMERAL (BIT1 0)))) /\ (forall y1 : nat, (num_divides y1 y0) -> (y1 = (NUMERAL (BIT1 0))) \/ (y1 = y0)))) x0.
Definition term14 := @eq nat (NUMERAL (BIT1 0)).
Definition term12 (x0 : nat) := (fun y0 : nat => (num_divides y0 (NUMERAL (BIT1 0))) = (y0 = (NUMERAL (BIT1 0)))) x0.
Definition term7 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (prime x0).
Definition term8 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ ((~ (x0 = (NUMERAL (BIT1 0)))) /\ (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0))).
Definition term9 (x0 : nat) := @eq Prop ((x0 = (NUMERAL (BIT1 0))) \/ (prime x0)).
Definition term21 (x0 : nat) := (x0 = (NUMERAL (BIT1 0))) -> x0 = (NUMERAL (BIT1 0)).
Definition term26 (x0 : Prop) := forall y0 : nat, x0.
Definition term31 (x0 : nat) := (fun y0 : Prop => y0 = True) ((forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0)) = (forall y0 : nat, (num_divides y0 x0) -> (y0 = (NUMERAL (BIT1 0))) \/ (y0 = x0))).
Definition term1 := NUMERAL (BIT1 0).
