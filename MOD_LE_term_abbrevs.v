Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term27 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1).
Definition term32 (x0 : nat) := forall y0 : nat, Peano.le (Nat.modulo x0 y0) x0.
Definition term25 (x0 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0)) x0.
Definition term12 (x0 : nat) := Nat.modulo x0 (NUMERAL 0).
Definition term11 (x0 : nat) := (fun y0 : nat => (Nat.modulo y0 (NUMERAL 0)) = y0) x0.
Definition term13 (x0 : nat) (x1 : nat) := Peano.le (Nat.modulo x0 x1).
Definition term20 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term29 (x0 : nat) (x1 : nat) := Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1).
Definition term24 := (forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) -> forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le x0 (Nat.add x0 y0).
Definition term26 (x0 : nat) (x1 : nat) := (fun y0 : nat => (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0)) x1.
Definition term9 (x0 : nat) := ~ (x0 = (NUMERAL 0)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x0 y0)) x1.
Definition term30 (x0 : nat) (x1 : nat) := Nat.mul (Nat.div x0 x1) x1.
Definition term14 (x0 : nat) (x1 : nat) := Peano.le (Nat.modulo x1 x0) x1.
Definition term10 (x0 : nat) := (fun y0 : nat => Peano.le y0 y0) x0.
Definition term23 := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> forall y1 : nat, (y1 = (Nat.add (Nat.mul (Nat.div y1 y0) y0) (Nat.modulo y1 y0))) /\ (Peano.lt (Nat.modulo y1 y0) y0).
Definition term33 := forall y0 : nat, forall y1 : nat, Peano.le (Nat.modulo y0 y1) y0.
Definition term15 := forall y0 : nat, forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1).
Definition term8 (x0 : nat) := (x0 = (NUMERAL 0)) \/ (~ (x0 = (NUMERAL 0))).
Definition term19 (x0 : nat) (x1 : nat) := (~ (x1 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1))) /\ (Peano.lt (Nat.modulo x0 x1) x1).
Definition term5 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term21 (x0 : nat) := forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add x0 x1).
Definition term16 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (~ (y1 = (NUMERAL 0))) -> (y0 = (Nat.add (Nat.mul (Nat.div y0 y1) y1) (Nat.modulo y0 y1))) /\ (Peano.lt (Nat.modulo y0 y1) y1)) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y0 (Nat.add y0 y1)) x0.
Definition term31 (x0 : nat) (x1 : nat) := Peano.le (Nat.modulo x0 x1) (Nat.add (Nat.modulo x0 x1) (Nat.mul (Nat.div x0 x1) x1)).
Definition term18 (x0 : nat) (x1 : nat) := (fun y0 : nat => (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0)) x1.
Definition term22 (x0 : nat) := (~ (x0 = (NUMERAL 0))) -> forall y0 : nat, (y0 = (Nat.add (Nat.mul (Nat.div y0 x0) x0) (Nat.modulo y0 x0))) /\ (Peano.lt (Nat.modulo y0 x0) x0).
Definition term17 (x0 : nat) := forall y0 : nat, (~ (y0 = (NUMERAL 0))) -> (x0 = (Nat.add (Nat.mul (Nat.div x0 y0) y0) (Nat.modulo x0 y0))) /\ (Peano.lt (Nat.modulo x0 y0) y0).
Definition term28 (x0 : nat) (x1 : nat) := Peano.le (Nat.modulo x0 x1) (Nat.add (Nat.mul (Nat.div x0 x1) x1) (Nat.modulo x0 x1)).
Definition term7 (x0 : nat) := (fun y0 : Prop => y0 \/ (~ y0)) (x0 = (NUMERAL 0)).
