Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term34 (x0 : nat) (x1 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x1) x0)) /\ (Peano.lt x0 x1).
Definition term25 := forall y0 : nat, (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0).
Definition term18 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) x0.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term33 (x0 : nat) (x1 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) x0)) /\ (Peano.lt x0 x1).
Definition term17 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := (exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x1) x2)) /\ (Peano.lt x2 x1)) -> (Nat.modulo x0 x1) = x2.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0.
Definition term26 (x0 : nat) := (fun y0 : nat => (Nat.mul (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0) x2.
Definition term21 (x0 : nat) (x1 : nat) := (exists y0 : nat, (x1 = (Nat.add (Nat.mul y0 x0) x1)) /\ (Peano.lt x1 x0)) -> (Nat.modulo x1 x0) = x1.
Definition term30 (x0 : nat) (x1 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0) x1.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) := exists y0 : nat, (x0 = (Nat.add (Nat.mul y0 x2) x1)) /\ (Peano.lt x1 x2).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (x0 = (Nat.add (Nat.mul x1 x3) x2)) /\ (Peano.lt x2 x3).
Definition term19 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1) x1.
Definition term28 (x0 : nat) := Nat.add (Nat.mul (NUMERAL 0) x0).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((x1 = (Nat.add (Nat.mul x0 x2) x3)) /\ (Peano.lt x3 x2)) -> (Nat.modulo x1 x2) = x3.
Definition term24 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((x1 = (Nat.add (Nat.mul x0 x2) y0)) /\ (Peano.lt y0 x2)) -> (Nat.modulo x1 x2) = y0) x3.
Definition term37 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> (Nat.modulo y0 y1) = y0.
Definition term16 := forall y0 : nat, forall y1 : nat, forall y2 : nat, (exists y3 : nat, (y0 = (Nat.add (Nat.mul y3 y1) y2)) /\ (Peano.lt y2 y1)) -> (Nat.modulo y0 y1) = y2.
Definition term15 (x0 : nat) := forall y0 : nat, forall y1 : nat, (exists y2 : nat, (x0 = (Nat.add (Nat.mul y2 y0) y1)) /\ (Peano.lt y1 y0)) -> (Nat.modulo x0 y0) = y1.
Definition term4 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1.
Definition term2 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2.
Definition term0 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3.
Definition term5 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((x0 = (Nat.add (Nat.mul y0 x1) y1)) /\ (Peano.lt y1 x1)) -> (Nat.modulo x0 x1) = y1) x2.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((x0 = (Nat.add (Nat.mul y1 y0) y2)) /\ (Peano.lt y2 y0)) -> (Nat.modulo x0 y0) = y2) x1.
Definition term22 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term23 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((y0 = (Nat.add (Nat.mul y2 y1) y3)) /\ (Peano.lt y3 y1)) -> (Nat.modulo y0 y1) = y3) -> (Nat.modulo x0 x1) = x2.
Definition term35 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) -> (Nat.modulo x1 x0) = x1.
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : nat, (exists y1 : nat, (x0 = (Nat.add (Nat.mul y1 x1) y0)) /\ (Peano.lt y0 x1)) -> (Nat.modulo x0 x1) = y0.
Definition term29 := Nat.add (NUMERAL 0).
Definition term32 (x0 : nat) (x1 : nat) := (x0 = (Nat.add (Nat.mul (NUMERAL 0) x1) x0)) /\ (Peano.lt x0 x1).
Definition term27 (x0 : nat) := Nat.mul (NUMERAL 0) x0.
Definition term31 (x0 : nat) (x1 : nat) := and (x1 = (Nat.add (Nat.mul (NUMERAL 0) x0) x1)).
Definition term36 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> (Nat.modulo x0 y0) = x0.
