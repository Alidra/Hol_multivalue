Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : nat) (x1 : nat) := Nat.modulo x0 (Nat.mul x1 (NUMERAL (BIT1 0))).
Definition term15 := (forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1))))).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.modulo (Nat.modulo y0 (Nat.mul y1 y2)) y1) = (Nat.modulo y0 y1)) x0.
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.modulo (Nat.modulo x0 (Nat.mul x1 y0)) x1) = (Nat.modulo x0 x1)) (NUMERAL (BIT1 0)).
Definition term10 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term18 (x0 : nat) := (fun y0 : nat => (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) x0.
Definition term9 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term24 (x0 : nat) (x1 : nat) := imp ((Nat.modulo (Nat.modulo x0 x1) x1) = (Nat.modulo x0 x1)).
Definition term23 (x0 : nat) (x1 : nat) := imp ((Nat.modulo (Nat.modulo x0 (Nat.mul x1 (NUMERAL (BIT1 0)))) x1) = (Nat.modulo x0 x1)).
Definition term3 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul x1 y0)) x1) = (Nat.modulo x0 x1).
Definition term12 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 x1) x1.
Definition term11 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul y0 y1)) y0) = (Nat.modulo x0 y0)) x1.
Definition term13 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 x1) x1).
Definition term27 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term17 := forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0.
Definition term26 (x0 : nat) (x1 : nat) := ((Nat.modulo (Nat.modulo x0 x1) x1) = (Nat.modulo x0 x1)) -> (Nat.modulo (Nat.modulo x0 x1) x1) = (Nat.modulo x0 x1).
Definition term25 (x0 : nat) (x1 : nat) := ((Nat.modulo (Nat.modulo x0 (Nat.mul x1 (NUMERAL (BIT1 0)))) x1) = (Nat.modulo x0 x1)) -> (Nat.modulo (Nat.modulo x0 x1) x1) = (Nat.modulo x0 x1).
Definition term28 (x0 : nat) := forall y0 : nat, (Nat.modulo (Nat.modulo x0 y0) y0) = (Nat.modulo x0 y0).
Definition term29 := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.modulo y0 y1) y1) = (Nat.modulo y0 y1).
Definition term1 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.modulo (Nat.modulo x0 (Nat.mul y0 y1)) y0) = (Nat.modulo x0 y0).
Definition term8 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term16 := (forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))).
Definition term19 (x0 : nat) := Nat.mul x0 (NUMERAL (BIT1 0)).
Definition term21 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul x1 (NUMERAL (BIT1 0)))).
Definition term6 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 (Nat.mul x1 (NUMERAL (BIT1 0)))) x1.
Definition term22 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 (Nat.mul x1 (NUMERAL (BIT1 0)))) x1).
Definition term14 := (forall y0 : nat, (Nat.mul y0 (NUMERAL 0)) = (NUMERAL 0)) /\ ((forall y0 : nat, (Nat.mul (NUMERAL (BIT1 0)) y0) = y0) /\ ((forall y0 : nat, (Nat.mul y0 (NUMERAL (BIT1 0))) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.mul (S y0) y1) = (Nat.add (Nat.mul y0 y1) y1)) /\ (forall y0 : nat, forall y1 : nat, (Nat.mul y0 (S y1)) = (Nat.add y0 (Nat.mul y0 y1)))))).
Definition term7 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
Definition term5 := NUMERAL (BIT1 0).
