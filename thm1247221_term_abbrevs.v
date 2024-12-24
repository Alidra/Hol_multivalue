Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term39 (x0 : nat) (x1 : nat) := Peano.le x0 (Nat.add (Nat.add x1 x0) x1).
Definition term14 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) (dist (@pair nat nat x2 x3)).
Definition term48 (x0 : nat) (x1 : nat) := Nat.add x0 (Nat.add x0 x1).
Definition term37 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add y0 x1)) x2.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, forall y2 : nat, (Nat.add y0 (Nat.add y1 y2)) = (Nat.add (Nat.add y0 y1) y2)) x0.
Definition term20 (x0 : nat) (x1 : nat) (x2 : nat) := Peano.le x0 (Nat.add x1 x2).
Definition term42 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le x0 (Nat.add x1 y0).
Definition term30 (x0 : nat) (x1 : nat) := fun y0 : nat => ((x0 = (Nat.add x1 y0)) -> (fun y1 : nat => Peano.le y1 (Nat.add x0 x1)) y0) /\ ((x1 = (Nat.add x0 y0)) -> (fun y1 : nat => Peano.le y1 (Nat.add x0 x1)) y0).
Definition term25 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.add x2 x0)) -> Peano.le x0 (Nat.add x1 x2).
Definition term22 (x0 : nat) (x1 : nat) (x2 : nat) := (x1 = (Nat.add x0 x2)) -> (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) x2.
Definition term21 (x0 : nat) (x1 : nat) (x2 : nat) := imp (x0 = (Nat.add x1 x2)).
Definition term34 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) (dist (@pair nat nat x0 x1))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 y0)) x1.
Definition term36 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le x0 (Nat.add y0 x1).
Definition term10 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add (Nat.add x0 x1) x2.
Definition term16 (x0 : nat) (x1 : nat) := fun y0 : nat => Peano.le y0 (Nat.add x0 x1).
Definition term7 (x0 : nat) (x1 : nat) := forall y0 : nat, (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0).
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1)) x1.
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x1 (Nat.add x0 y0)) (Nat.add x0 x1).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le x1 (Nat.add y0 x0)) (Nat.add x0 x1).
Definition term26 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x0 = (Nat.add x1 x2)) -> (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) x2).
Definition term31 (x0 : nat) (x1 : nat) := fun y0 : nat => ((x0 = (Nat.add x1 y0)) -> Peano.le y0 (Nat.add x0 x1)) /\ ((x1 = (Nat.add x0 y0)) -> Peano.le y0 (Nat.add x0 x1)).
Definition term17 (x0 : nat) (x1 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) (dist (@pair nat nat x0 x1)).
Definition term35 (x0 : nat) (x1 : nat) := @eq Prop (Peano.le (dist (@pair nat nat x0 x1)) (Nat.add x0 x1)).
Definition term47 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x1 x0) x1.
Definition term50 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add (Nat.add x0 x0) x1).
Definition term45 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 (Nat.add x0 x1)).
Definition term52 := forall y0 : nat, forall y1 : nat, Peano.le (dist (@pair nat nat y0 y1)) (Nat.add y0 y1).
Definition term5 (x0 : nat) := forall y0 : nat, forall y1 : nat, (Nat.add x0 (Nat.add y0 y1)) = (Nat.add (Nat.add x0 y0) y1).
Definition term51 (x0 : nat) := forall y0 : nat, Peano.le (dist (@pair nat nat x0 y0)) (Nat.add x0 y0).
Definition term33 (x0 : nat) (x1 : nat) := Peano.le (dist (@pair nat nat x0 x1)) (Nat.add x0 x1).
Definition term28 (x0 : nat) (x1 : nat) (x2 : nat) := ((x0 = (Nat.add x1 x2)) -> (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) x2) /\ ((x1 = (Nat.add x0 x2)) -> (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) x2).
Definition term41 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop (Peano.le x0 (Nat.add x1 x2)).
Definition term43 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le x0 (Nat.add x1 y0)) x2.
Definition term12 (x0 : nat) := forall y0 : nat, (Nat.add x0 y0) = (Nat.add y0 x0).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 y0) = (Nat.add y0 x0)) x1.
Definition term9 (x0 : nat) (x1 : nat) (x2 : nat) := Nat.add x0 (Nat.add x1 x2).
Definition term3 (x0 : nat) (x1 : nat) := Peano.le x1 (Nat.add x0 x1).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 y1) = (Nat.add y1 y0)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, Peano.le y1 (Nat.add y0 y1)) x0.
Definition term49 (x0 : nat) (x1 : nat) := Nat.add (Nat.add x0 x0) x1.
Definition term27 (x0 : nat) (x1 : nat) (x2 : nat) := and ((x1 = (Nat.add x2 x0)) -> Peano.le x0 (Nat.add x1 x2)).
Definition term18 (x0 : nat) (x1 : nat) := forall y0 : nat, ((x0 = (Nat.add x1 y0)) -> (fun y1 : nat => Peano.le y1 (Nat.add x0 x1)) y0) /\ ((x1 = (Nat.add x0 y0)) -> (fun y1 : nat => Peano.le y1 (Nat.add x0 x1)) y0).
Definition term15 (x0 : nat) (x1 : nat) (x2 : nat) (x3 : nat) := forall y0 : nat, ((x1 = (Nat.add x0 y0)) -> (fun y1 : nat => Peano.le y1 (Nat.add x2 x3)) y0) /\ ((x0 = (Nat.add x1 y0)) -> (fun y1 : nat => Peano.le y1 (Nat.add x2 x3)) y0).
Definition term23 (x0 : nat) (x1 : nat) (x2 : nat) := (x2 = (Nat.add x1 x0)) -> Peano.le x0 (Nat.add x1 x2).
Definition term8 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => (Nat.add x0 (Nat.add x1 y0)) = (Nat.add (Nat.add x0 x1) y0)) x2.
Definition term46 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => Peano.le x0 (Nat.add x1 y0)) x2).
Definition term40 (x0 : nat) (x1 : nat) (x2 : nat) := @eq Prop ((fun y0 : nat => Peano.le x0 (Nat.add y0 x1)) x2).
Definition term24 (x0 : nat) (x1 : nat) (x2 : nat) := (x0 = (Nat.add x1 x2)) -> (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) x2.
Definition term19 (x0 : nat) (x1 : nat) (x2 : nat) := (fun y0 : nat => Peano.le y0 (Nat.add x0 x1)) x2.
Definition term1 (x0 : nat) := forall y0 : nat, Peano.le y0 (Nat.add x0 y0).
Definition term29 (x0 : nat) (x1 : nat) (x2 : nat) := ((x1 = (Nat.add x2 x0)) -> Peano.le x0 (Nat.add x1 x2)) /\ ((x2 = (Nat.add x1 x0)) -> Peano.le x0 (Nat.add x1 x2)).
Definition term32 (x0 : nat) (x1 : nat) := forall y0 : nat, ((x0 = (Nat.add x1 y0)) -> Peano.le y0 (Nat.add x0 x1)) /\ ((x1 = (Nat.add x0 y0)) -> Peano.le y0 (Nat.add x0 x1)).
