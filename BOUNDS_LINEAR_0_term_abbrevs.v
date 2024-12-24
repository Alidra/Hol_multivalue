Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := (fun y0 : nat => (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0))) x0.
Definition term6 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (forall y3 : nat, Peano.le (Nat.mul y0 y3) (Nat.add (Nat.mul y1 y3) y2)) = (Peano.le y0 y1)) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) (Nat.add (Nat.mul (NUMERAL 0) x1) x2).
Definition term17 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0) x1.
Definition term24 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul (NUMERAL 0) y0) x1)).
Definition term15 (x0 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (forall y2 : nat, Peano.le (Nat.mul x0 y2) (Nat.add (Nat.mul y0 y2) y1)) = (Peano.le x0 y0)) (NUMERAL 0).
Definition term5 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term31 := forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.le (Nat.mul y0 y2) y1) = (y0 = (NUMERAL 0)).
Definition term10 (x0 : nat) := forall y0 : nat, forall y1 : nat, (forall y2 : nat, Peano.le (Nat.mul x0 y2) (Nat.add (Nat.mul y0 y2) y1)) = (Peano.le x0 y0).
Definition term29 (x0 : nat) (x1 : nat) := ((forall y0 : nat, Peano.le (Nat.mul x1 y0) x0) = (x1 = (NUMERAL 0))) -> (forall y0 : nat, Peano.le (Nat.mul x1 y0) x0) = (x1 = (NUMERAL 0)).
Definition term28 (x0 : nat) (x1 : nat) := ((forall y0 : nat, Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul (NUMERAL 0) y0) x0)) = (Peano.le x1 (NUMERAL 0))) -> (forall y0 : nat, Peano.le (Nat.mul x1 y0) x0) = (x1 = (NUMERAL 0)).
Definition term23 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x0 y0) x1.
Definition term22 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul x0 y0) x1.
Definition term30 (x0 : nat) := forall y0 : nat, (forall y1 : nat, Peano.le (Nat.mul x0 y1) y0) = (x0 = (NUMERAL 0)).
Definition term12 (x0 : nat) := forall y0 : nat, (forall y1 : nat, Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul (NUMERAL 0) y1) y0)) = (Peano.le x0 (NUMERAL 0)).
Definition term3 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term4 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x0 x1) x2.
Definition term25 (x0 : nat) (x1 : nat) := @eq Prop (forall y0 : nat, Peano.le (Nat.mul x0 y0) x1).
Definition term16 := Nat.add (NUMERAL 0).
Definition term18 (x0 : nat) (x1 : nat) := Peano.le (Nat.mul x0 x1).
Definition term26 (x0 : nat) (x1 : nat) := imp ((forall y0 : nat, Peano.le (Nat.mul x1 y0) (Nat.add (Nat.mul (NUMERAL 0) y0) x0)) = (Peano.le x1 (NUMERAL 0))).
Definition term0 := forall y0 : nat, (Peano.le y0 (NUMERAL 0)) = (y0 = (NUMERAL 0)).
Definition term27 (x0 : nat) (x1 : nat) := imp ((forall y0 : nat, Peano.le (Nat.mul x1 y0) x0) = (x1 = (NUMERAL 0))).
Definition term8 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, Peano.le (Nat.mul x0 y1) (Nat.add (Nat.mul (NUMERAL 0) y1) y0)) = (Peano.le x0 (NUMERAL 0))) x1.
Definition term2 (x0 : nat) := Peano.le x0 (NUMERAL 0).
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul (NUMERAL 0) y0) x1).
Definition term21 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le (Nat.mul x0 y0) (Nat.add (Nat.mul (NUMERAL 0) y0) x1).
