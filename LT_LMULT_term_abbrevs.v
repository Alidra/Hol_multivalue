Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term33 (x0 : nat) (x1 : nat) := ~ (x0 = x1).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := ((Peano.le x1 x1) /\ (Peano.le x0 x2)) -> Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term39 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Nat.mul y0 y1) = (Nat.mul y0 y2)) = ((y0 = (NUMERAL 0)) \/ (y1 = y2))) x0.
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3)) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0)) x3.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term15 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3).
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((~ (x0 = (NUMERAL 0))) /\ ((Peano.le x1 x2) /\ (~ (x1 = x2)))).
Definition term48 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((Nat.mul x1 x0) = (Nat.mul x1 x2)).
Definition term44 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) \/ (x1 = x2).
Definition term41 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1))) x1.
Definition term32 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le x0 x0) /\ (Peano.le x1 x2).
Definition term35 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term46 (x0 : nat) (x1 : nat) := (~ (x0 = x1)) -> (x0 = x1) = False.
Definition term47 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term51 := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((~ (y0 = (NUMERAL 0))) /\ (Peano.lt y1 y2)) -> Peano.lt (Nat.mul y0 y1) (Nat.mul y0 y2).
Definition term50 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt y0 y1)) -> Peano.lt (Nat.mul x0 y0) (Nat.mul x0 y1).
Definition term40 (x0 : nat) := forall y0 : nat, forall y1 : nat, ((Nat.mul x0 y0) = (Nat.mul x0 y1)) = ((x0 = (NUMERAL 0)) \/ (y0 = y1)).
Definition term14 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.le y1 y3)) -> Peano.le (Nat.mul y0 y1) (Nat.mul y2 y3).
Definition term13 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul x0 y0) (Nat.mul y1 y2).
Definition term12 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.mul x0 x1) (Nat.mul y0 y1).
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1).
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2).
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y1) /\ (Peano.le y2 y3)) -> Peano.le (Nat.mul y0 y2) (Nat.mul y1 y3).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.le x1 y1)) -> Peano.le (Nat.mul x0 x1) (Nat.mul y0 y1)) x2.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 x1) /\ (Peano.le y0 y1)) -> Peano.le (Nat.mul x0 y0) (Nat.mul x1 y1)) x2.
Definition term30 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL 0))) /\ (Peano.lt x0 x2)) -> Peano.lt (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.le y0 y2)) -> Peano.le (Nat.mul x0 y0) (Nat.mul y1 y2)) x1.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y0) /\ (Peano.le y1 y2)) -> Peano.le (Nat.mul x0 y1) (Nat.mul y0 y2)) x1.
Definition term22 (x0 : nat) (x1 : nat) := (Peano.le x0 x1) /\ (~ (x0 = x1)).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) /\ ((Peano.le x1 x2) /\ (~ (x1 = x2))).
Definition term42 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0)).
Definition term38 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.le x1 x3)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 x3).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := (Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2)) /\ (~ ((Nat.mul x1 x0) = (Nat.mul x1 x2))).
Definition term36 (x0 : nat) := and (Peano.le x0 x0).
Definition term23 (x0 : nat) := and (~ (x0 = (NUMERAL 0))).
Definition term20 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) = ((Peano.le x0 y0) /\ (~ (x0 = y0))).
Definition term31 (x0 : nat) (x1 : nat) (x2 : nat) := ((~ (x1 = (NUMERAL 0))) /\ ((Peano.le x0 x2) /\ (~ (x0 = x2)))) -> (Peano.le (Nat.mul x1 x0) (Nat.mul x1 x2)) /\ (~ ((Nat.mul x1 x0) = (Nat.mul x1 x2))).
Definition term19 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) = ((Peano.le y0 y1) /\ (~ (y0 = y1)))) x0.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.le x2 x3).
Definition term49 (x0 : nat) (x1 : nat) := forall y0 : nat, ((~ (x1 = (NUMERAL 0))) /\ (Peano.lt x0 y0)) -> Peano.lt (Nat.mul x1 x0) (Nat.mul x1 y0).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.le x1 y0)) -> Peano.le (Nat.mul x0 x1) (Nat.mul x2 y0).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => ((Nat.mul x0 x1) = (Nat.mul x0 y0)) = ((x0 = (NUMERAL 0)) \/ (x1 = y0))) x2.
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.lt (Nat.mul x1 x0) (Nat.mul x1 x2).
Definition term45 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term21 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) = ((Peano.le x0 y0) /\ (~ (x0 = y0)))) x1.
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := imp ((~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 x2)).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) /\ (Peano.lt x1 x2).
