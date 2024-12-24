Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ (((x3 = (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (x2 = x0))) \/ ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))).
Definition term25 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) := forall y0 : nat, (((x1 = (NUMERAL 0)) /\ ((x3 = (NUMERAL 0)) /\ (y0 = x0))) \/ ((x0 = (Nat.add (Nat.mul x3 x1) y0)) /\ (Peano.lt y0 x1))) -> x2 x3 y0.
Definition term1 (x0 : nat) (x1 : nat) (x2 : nat) := (~ (x0 = (NUMERAL 0))) \/ (~ (x1 = x2)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := or (~ (((x3 = (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (x2 = x0))) \/ ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)))).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term23 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) := fun y0 : nat => (((x1 = (NUMERAL 0)) /\ ((x3 = (NUMERAL 0)) /\ (y0 = x0))) \/ ((x0 = (Nat.add (Nat.mul x3 x1) y0)) /\ (Peano.lt y0 x1))) -> x2 x3 y0.
Definition term28 (x0 : nat) (x1 : nat) (x2 : type1605) := fun y0 : nat => forall y1 : nat, (((~ (x1 = (NUMERAL 0))) \/ ((~ (y0 = (NUMERAL 0))) \/ (~ (y1 = x0)))) /\ ((~ (x0 = (Nat.add (Nat.mul y0 x1) y1))) \/ (~ (Peano.lt y1 x1)))) \/ (x2 y0 y1).
Definition term27 (x0 : nat) (x1 : nat) (x2 : type1605) := fun y0 : nat => forall y1 : nat, (((x1 = (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (y1 = x0))) \/ ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1))) -> x2 y0 y1.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((x0 = (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (x2 = x3))).
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = x2).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((~ (x3 = (NUMERAL 0))) \/ ((~ (x1 = (NUMERAL 0))) \/ (~ (x2 = x0)))) /\ ((~ (x0 = (Nat.add (Nat.mul x1 x3) x2))) \/ (~ (Peano.lt x2 x3))).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ~ ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = (Nat.add (Nat.mul x1 x3) x2))) \/ (~ (Peano.lt x2 x3)).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := and (~ ((x0 = (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (x2 = x3)))).
Definition term21 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (((x1 = (NUMERAL 0)) /\ ((x3 = (NUMERAL 0)) /\ (x4 = x0))) \/ ((x0 = (Nat.add (Nat.mul x3 x1) x4)) /\ (Peano.lt x4 x1))) -> x2 x3 x4.
Definition term30 (x0 : nat) (x1 : nat) (x2 : type1605) := forall y0 : nat, forall y1 : nat, (((~ (x1 = (NUMERAL 0))) \/ ((~ (y0 = (NUMERAL 0))) \/ (~ (y1 = x0)))) /\ ((~ (x0 = (Nat.add (Nat.mul y0 x1) y1))) \/ (~ (Peano.lt y1 x1)))) \/ (x2 y0 y1).
Definition term29 (x0 : nat) (x1 : nat) (x2 : type1605) := forall y0 : nat, forall y1 : nat, (((x1 = (NUMERAL 0)) /\ ((y0 = (NUMERAL 0)) /\ (y1 = x0))) \/ ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1))) -> x2 y0 y1.
Definition term32 (x0 : type1605) (x1 : nat) (x2 : nat) := x0 (Nat.div x1 x2) (Nat.modulo x1 x2).
Definition term19 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (~ (((x1 = (NUMERAL 0)) /\ ((x3 = (NUMERAL 0)) /\ (x4 = x0))) \/ ((x0 = (Nat.add (Nat.mul x3 x1) x4)) /\ (Peano.lt x4 x1)))) \/ (x2 x3 x4).
Definition term26 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) := forall y0 : nat, (((~ (x1 = (NUMERAL 0))) \/ ((~ (x3 = (NUMERAL 0))) \/ (~ (y0 = x0)))) /\ ((~ (x0 = (Nat.add (Nat.mul x3 x1) y0))) \/ (~ (Peano.lt y0 x1)))) \/ (x2 x3 y0).
Definition term2 (x0 : nat) := or (~ (x0 = (NUMERAL 0))).
Definition term24 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) := fun y0 : nat => (((~ (x1 = (NUMERAL 0))) \/ ((~ (x3 = (NUMERAL 0))) \/ (~ (y0 = x0)))) /\ ((~ (x0 = (Nat.add (Nat.mul x3 x1) y0))) \/ (~ (Peano.lt y0 x1)))) \/ (x2 x3 y0).
Definition term31 (x0 : type1605) (x1 : nat) (x2 : nat) := @eq Prop (x0 (Nat.div x1 x2) (Nat.modulo x1 x2)).
Definition term3 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = (NUMERAL 0))) \/ (~ ((x1 = (NUMERAL 0)) /\ (x2 = x3))).
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := or (((~ (x3 = (NUMERAL 0))) \/ ((~ (x1 = (NUMERAL 0))) \/ (~ (x2 = x0)))) /\ ((~ (x0 = (Nat.add (Nat.mul x1 x3) x2))) \/ (~ (Peano.lt x2 x3)))).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ ((x3 = (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (x2 = x0)))) /\ (~ ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3))).
Definition term20 (x0 : nat) (x1 : nat) (x2 : type1605) (x3 : nat) (x4 : nat) := (((~ (x1 = (NUMERAL 0))) \/ ((~ (x3 = (NUMERAL 0))) \/ (~ (x4 = x0)))) /\ ((~ (x0 = (Nat.add (Nat.mul x3 x1) x4))) \/ (~ (Peano.lt x4 x1)))) \/ (x2 x3 x4).
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := and ((~ (x0 = (NUMERAL 0))) \/ ((~ (x1 = (NUMERAL 0))) \/ (~ (x2 = x3)))).
Definition term4 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (~ (x0 = (NUMERAL 0))) \/ ((~ (x1 = (NUMERAL 0))) \/ (~ (x2 = x3))).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (x2 = x3)).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.mul x0 x1) x2.
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x3 = (NUMERAL 0)) /\ ((x1 = (NUMERAL 0)) /\ (x2 = x0))) \/ ((x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3)).
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat) := ~ ((x0 = (NUMERAL 0)) /\ (x1 = x2)).
