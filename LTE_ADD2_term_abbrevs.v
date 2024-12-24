Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term7 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.le x0 x1) /\ (Peano.lt x2 x3).
Definition term30 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y0 y2) /\ (Peano.lt y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3)) x0.
Definition term6 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (Peano.lt x0 x1) /\ (Peano.le x2 x3).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((Peano.lt x0 x1) /\ (Peano.le x2 x3)).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) := fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.lt x1 x2)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 x2).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y0 /\ y1) = (y1 /\ y0)) x0.
Definition term10 (x0 : nat) (x1 : nat) := Peano.lt (Nat.add x0 x1).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (x0 /\ y0) = (y0 /\ x0)) x1.
Definition term33 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term31 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term29 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add y1 y0) (Nat.add y3 y2).
Definition term28 := forall y0 : nat, forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term25 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.lt x0 y1)) -> Peano.lt (Nat.add y0 x0) (Nat.add y2 y1).
Definition term24 (x0 : nat) := forall y0 : nat, forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
Definition term21 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.le x0 y1) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add y1 y0).
Definition term20 (x0 : nat) (x1 : nat) := forall y0 : nat, forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term34 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le x0 y0) /\ (Peano.lt x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1)) x2.
Definition term32 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le x0 y1) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2)) x1.
Definition term36 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => ((Peano.le x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0)) x3.
Definition term13 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.le x0 x2) /\ (Peano.lt x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term12 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := ((Peano.lt x0 x2) /\ (Peano.le x1 x3)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term4 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term5 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term11 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := Peano.lt (Nat.add x0 x1) (Nat.add x2 x3).
Definition term3 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term35 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 x2) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term17 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.lt x1 x2)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 x2).
Definition term16 (x0 : nat) (x1 : nat) (x2 : nat) := forall y0 : nat, ((Peano.lt x0 x2) /\ (Peano.le x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add x2 y0).
Definition term1 (x0 : Prop) := forall y0 : Prop, (x0 /\ y0) = (y0 /\ x0).
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := imp ((Peano.le x0 x1) /\ (Peano.lt x2 x3)).
Definition term19 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.le x0 y1) /\ (Peano.lt x1 y0)) -> Peano.lt (Nat.add x0 x1) (Nat.add y1 y0).
Definition term18 (x0 : nat) (x1 : nat) := fun y0 : nat => forall y1 : nat, ((Peano.lt x0 y0) /\ (Peano.le x1 y1)) -> Peano.lt (Nat.add x0 x1) (Nat.add y0 y1).
Definition term27 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.le y1 y3) /\ (Peano.lt y0 y2)) -> Peano.lt (Nat.add y1 y0) (Nat.add y3 y2).
Definition term26 := fun y0 : nat => forall y1 : nat, forall y2 : nat, forall y3 : nat, ((Peano.lt y0 y2) /\ (Peano.le y1 y3)) -> Peano.lt (Nat.add y0 y1) (Nat.add y2 y3).
Definition term23 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.le y0 y2) /\ (Peano.lt x0 y1)) -> Peano.lt (Nat.add y0 x0) (Nat.add y2 y1).
Definition term22 (x0 : nat) := fun y0 : nat => forall y1 : nat, forall y2 : nat, ((Peano.lt x0 y1) /\ (Peano.le y0 y2)) -> Peano.lt (Nat.add x0 y0) (Nat.add y1 y2).
