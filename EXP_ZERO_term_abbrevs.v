Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 := @eq nat (NUMERAL 0).
Definition term8 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (NUMERAL 0).
Definition term3 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) := (x1 -> (fun y0 : nat => (Nat.pow (NUMERAL 0) x2) = y0) x0) /\ ((~ x1) -> (fun y0 : nat => (Nat.pow (NUMERAL 0) x2) = y0) x3).
Definition term30 := or ((NUMERAL 0) = (NUMERAL (BIT1 0))).
Definition term2 (x0 : nat) (x1 : Prop) (x2 : nat) (x3 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (@COND nat x1 x2 x3).
Definition term12 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (Nat.pow (NUMERAL 0) x0) = (NUMERAL 0).
Definition term22 (x0 : nat) := @eq Prop ((Nat.pow (NUMERAL 0) x0) = (@COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term19 (x0 : nat) := ((x0 = (NUMERAL 0)) -> (Nat.pow (NUMERAL 0) x0) = (NUMERAL (BIT1 0))) /\ ((~ (x0 = (NUMERAL 0))) -> (Nat.pow (NUMERAL 0) x0) = (NUMERAL 0)).
Definition term9 (x0 : nat) := Nat.pow (NUMERAL 0) x0.
Definition term18 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> (Nat.pow (NUMERAL 0) x0) = (NUMERAL (BIT1 0))).
Definition term39 := forall y0 : nat, (Nat.pow (NUMERAL 0) y0) = (@COND nat (y0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term0 (x0 : nat -> Prop) (x1 : Prop) (x2 : nat) (x3 : nat) := x0 (@COND nat x1 x2 x3).
Definition term10 (x0 : nat) := imp (~ (x0 = (NUMERAL 0))).
Definition term11 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (NUMERAL 0).
Definition term25 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0))).
Definition term23 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term27 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL (BIT1 0))) \/ (x1 = (NUMERAL 0)).
Definition term1 (x0 : nat) (x1 : Prop) (x2 : nat -> Prop) (x3 : nat) := (x1 -> x2 x0) /\ ((~ x1) -> x2 x3).
Definition term6 (x0 : nat) := ((x0 = (NUMERAL 0)) -> (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (NUMERAL (BIT1 0))) /\ ((~ (x0 = (NUMERAL 0))) -> (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (NUMERAL 0)).
Definition term14 (x0 : nat) := imp (x0 = (NUMERAL 0)).
Definition term37 (x0 : nat) := ((NUMERAL 0) = (NUMERAL 0)) /\ (~ (x0 = (NUMERAL 0))).
Definition term38 := and ((NUMERAL 0) = (NUMERAL 0)).
Definition term35 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (~ (x1 = (NUMERAL 0))).
Definition term21 (x0 : nat) := @eq Prop ((fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (@COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0))).
Definition term16 (x0 : nat) := (x0 = (NUMERAL 0)) -> (Nat.pow (NUMERAL 0) x0) = (NUMERAL (BIT1 0)).
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0))))) x1.
Definition term20 (x0 : nat) := @COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0).
Definition term31 := ((NUMERAL 0) = (NUMERAL (BIT1 0))) \/ True.
Definition term4 (x0 : nat) := fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0.
Definition term13 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (NUMERAL (BIT1 0)).
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.pow x0 y0) = (NUMERAL (BIT1 0))) = ((x0 = (NUMERAL (BIT1 0))) \/ (y0 = (NUMERAL 0)))) x1.
Definition term32 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (~ (y1 = (NUMERAL 0))))) x0.
Definition term24 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.pow y0 y1) = (NUMERAL (BIT1 0))) = ((y0 = (NUMERAL (BIT1 0))) \/ (y1 = (NUMERAL 0)))) x0.
Definition term5 (x0 : nat) := (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (@COND nat (x0 = (NUMERAL 0)) (NUMERAL (BIT1 0)) (NUMERAL 0)).
Definition term36 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term28 (x0 : nat) := ((NUMERAL 0) = (NUMERAL (BIT1 0))) \/ (x0 = (NUMERAL 0)).
Definition term17 (x0 : nat) := and ((x0 = (NUMERAL 0)) -> (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (NUMERAL (BIT1 0))).
Definition term7 := NUMERAL (BIT1 0).
Definition term15 (x0 : nat) := (x0 = (NUMERAL 0)) -> (fun y0 : nat => (Nat.pow (NUMERAL 0) x0) = y0) (NUMERAL (BIT1 0)).
Definition term33 (x0 : nat) := forall y0 : nat, ((Nat.pow x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (~ (y0 = (NUMERAL 0)))).
