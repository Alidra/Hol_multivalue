Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) /\ (Peano.lt x2 x3).
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) /\ (Peano.le x2 x3).
Definition term19 := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term6 := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term5 (x0 : nat) (x1 : nat) := (forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) -> Peano.le x0 x1.
Definition term18 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term27 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term26 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term25 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term11 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term9 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term7 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term0 := forall y0 : nat, forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1.
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt x0 y0) -> Peano.le x0 y0) x1.
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.lt x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.le x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term21 (x0 : nat) (x1 : nat) := and (Peano.lt x0 x1).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term1 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt y0 y1) -> Peano.le y0 y1) x0.
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term22 (x0 : nat) (x1 : nat) := True /\ (Peano.le x0 x1).
Definition term4 (x0 : nat) (x1 : nat) := (Peano.lt x0 x1) -> Peano.le x0 x1.
Definition term2 (x0 : nat) := forall y0 : nat, (Peano.lt x0 y0) -> Peano.le x0 y0.
