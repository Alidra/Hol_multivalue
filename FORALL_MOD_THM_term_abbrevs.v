Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term29 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term32 := fun y0 : nat -> Prop => True.
Definition term15 (x0 : nat -> Prop) (x1 : nat) (x2 : Prop) := ((~ (x1 = (NUMERAL 0))) = (~ (x1 = (NUMERAL 0)))) -> ((~ (x1 = (NUMERAL 0))) -> ((forall y0 : nat, x0 (Nat.modulo y0 x1)) = (forall y0 : nat, (Peano.lt y0 x1) -> x0 y0)) = x2) -> ((~ (x1 = (NUMERAL 0))) -> (forall y0 : nat, x0 (Nat.modulo y0 x1)) = (forall y0 : nat, (Peano.lt y0 x1) -> x0 y0)) = ((~ (x1 = (NUMERAL 0))) -> x2).
Definition term20 (x0 : nat -> Prop) (x1 : nat) := @eq Prop (forall y0 : nat, x0 (Nat.modulo y0 x1)).
Definition term21 (x0 : nat) (x1 : nat -> Prop) := (~ (x0 = (NUMERAL 0))) -> ((forall y0 : nat, x1 (Nat.modulo y0 x0)) = (forall y0 : nat, (Peano.lt y0 x0) -> x1 y0)) = True.
Definition term27 (x0 : nat -> Prop) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (forall y1 : nat, x0 (Nat.modulo y1 y0)) = (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1).
Definition term9 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term5 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term31 := fun y0 : nat -> Prop => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (forall y2 : nat, y0 (Nat.modulo y2 y1)) = (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2).
Definition term2 (x0 : nat -> Prop) (x1 : nat) := (fun y0 : nat => (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1) = ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, x0 (Nat.modulo y1 y0)))) x1.
Definition term34 := forall y0 : nat -> Prop, True.
Definition term18 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term13 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((~ (x0 = (NUMERAL 0))) = x2) -> (x2 -> ((forall y1 : nat, x1 (Nat.modulo y1 x0)) = (forall y1 : nat, (Peano.lt y1 x0) -> x1 y1)) = y0) -> ((~ (x0 = (NUMERAL 0))) -> (forall y1 : nat, x1 (Nat.modulo y1 x0)) = (forall y1 : nat, (Peano.lt y1 x0) -> x1 y1)) = (x2 -> y0)) x3.
Definition term28 := forall y0 : nat, True.
Definition term4 (x0 : nat -> Prop) (x1 : nat) := (x1 = (NUMERAL 0)) \/ (forall y0 : nat, x0 (Nat.modulo y0 x1)).
Definition term25 (x0 : nat -> Prop) := fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (forall y1 : nat, x0 (Nat.modulo y1 y0)) = (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1).
Definition term19 (x0 : nat -> Prop) (x1 : nat) := False \/ (forall y0 : nat, x0 (Nat.modulo y0 x1)).
Definition term26 := fun y0 : nat => True.
Definition term1 (x0 : nat -> Prop) := forall y0 : nat, (forall y1 : nat, (Peano.lt y1 y0) -> x0 y1) = ((y0 = (NUMERAL 0)) \/ (forall y1 : nat, x0 (Nat.modulo y1 y0))).
Definition term12 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) := forall y0 : Prop, ((~ (x0 = (NUMERAL 0))) = x2) -> (x2 -> ((forall y1 : nat, x1 (Nat.modulo y1 x0)) = (forall y1 : nat, (Peano.lt y1 x0) -> x1 y1)) = y0) -> ((~ (x0 = (NUMERAL 0))) -> (forall y1 : nat, x1 (Nat.modulo y1 x0)) = (forall y1 : nat, (Peano.lt y1 x0) -> x1 y1)) = (x2 -> y0).
Definition term6 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term14 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) (x3 : Prop) := ((~ (x0 = (NUMERAL 0))) = x2) -> (x2 -> ((forall y0 : nat, x1 (Nat.modulo y0 x0)) = (forall y0 : nat, (Peano.lt y0 x0) -> x1 y0)) = x3) -> ((~ (x0 = (NUMERAL 0))) -> (forall y0 : nat, x1 (Nat.modulo y0 x0)) = (forall y0 : nat, (Peano.lt y0 x0) -> x1 y0)) = (x2 -> x3).
Definition term10 (x0 : nat -> Prop) (x1 : nat) := forall y0 : nat, x0 (Nat.modulo y0 x1).
Definition term8 (x0 : nat) (x1 : nat -> Prop) := forall y0 : Prop, forall y1 : Prop, ((~ (x0 = (NUMERAL 0))) = y0) -> (y0 -> ((forall y2 : nat, x1 (Nat.modulo y2 x0)) = (forall y2 : nat, (Peano.lt y2 x0) -> x1 y2)) = y1) -> ((~ (x0 = (NUMERAL 0))) -> (forall y2 : nat, x1 (Nat.modulo y2 x0)) = (forall y2 : nat, (Peano.lt y2 x0) -> x1 y2)) = (y0 -> y1).
Definition term7 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term33 := forall y0 : nat -> Prop, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (forall y2 : nat, y0 (Nat.modulo y2 y1)) = (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2).
Definition term3 (x0 : nat) (x1 : nat -> Prop) := forall y0 : nat, (Peano.lt y0 x0) -> x1 y0.
Definition term35 (x0 : Prop) := forall y0 : nat -> Prop, x0.
Definition term23 (x0 : nat) (x1 : nat -> Prop) := (~ (x0 = (NUMERAL 0))) -> (forall y0 : nat, x1 (Nat.modulo y0 x0)) = (forall y0 : nat, (Peano.lt y0 x0) -> x1 y0).
Definition term22 (x0 : nat -> Prop) (x1 : nat) := ((~ (x1 = (NUMERAL 0))) -> ((forall y0 : nat, x0 (Nat.modulo y0 x1)) = (forall y0 : nat, (Peano.lt y0 x1) -> x0 y0)) = True) -> ((~ (x1 = (NUMERAL 0))) -> (forall y0 : nat, x0 (Nat.modulo y0 x1)) = (forall y0 : nat, (Peano.lt y0 x1) -> x0 y0)) = ((~ (x1 = (NUMERAL 0))) -> True).
Definition term24 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> True.
Definition term17 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> (x0 = (NUMERAL 0)) = False.
Definition term30 (x0 : Prop) := forall y0 : nat, x0.
Definition term0 (x0 : nat -> Prop) := (fun y0 : nat -> Prop => forall y1 : nat, (forall y2 : nat, (Peano.lt y2 y1) -> y0 y2) = ((y1 = (NUMERAL 0)) \/ (forall y2 : nat, y0 (Nat.modulo y2 y1)))) x0.
Definition term16 (x0 : nat -> Prop) (x1 : nat) (x2 : Prop) := ((~ (x1 = (NUMERAL 0))) -> ((forall y0 : nat, x0 (Nat.modulo y0 x1)) = (forall y0 : nat, (Peano.lt y0 x1) -> x0 y0)) = x2) -> ((~ (x1 = (NUMERAL 0))) -> (forall y0 : nat, x0 (Nat.modulo y0 x1)) = (forall y0 : nat, (Peano.lt y0 x1) -> x0 y0)) = ((~ (x1 = (NUMERAL 0))) -> x2).
Definition term11 (x0 : nat) (x1 : nat -> Prop) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((~ (x0 = (NUMERAL 0))) = y0) -> (y0 -> ((forall y2 : nat, x1 (Nat.modulo y2 x0)) = (forall y2 : nat, (Peano.lt y2 x0) -> x1 y2)) = y1) -> ((~ (x0 = (NUMERAL 0))) -> (forall y2 : nat, x1 (Nat.modulo y2 x0)) = (forall y2 : nat, (Peano.lt y2 x0) -> x1 y2)) = (y0 -> y1)) x2.
