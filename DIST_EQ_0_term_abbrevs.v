Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0)) x1.
Definition term3 (x0 : nat) (x1 : nat) := (Peano.le x1 x0) /\ (Peano.le x0 x1).
Definition term27 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0)) x1.
Definition term25 (x0 : nat) := forall y0 : nat, ((dist (@pair nat nat x0 y0)) = (NUMERAL 0)) = (x0 = y0).
Definition term5 (x0 : nat) := forall y0 : nat, ((Nat.sub x0 y0) = (NUMERAL 0)) = (Peano.le x0 y0).
Definition term1 (x0 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x0)) = (x0 = y0).
Definition term14 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term8 (x0 : nat) := forall y0 : nat, ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0))).
Definition term21 (x0 : nat) (x1 : nat) := @eq Prop ((dist (@pair nat nat x0 x1)) = (NUMERAL 0)).
Definition term10 (x0 : nat) (x1 : nat) := (x0 = (NUMERAL 0)) /\ (x1 = (NUMERAL 0)).
Definition term29 := fun y0 : nat => forall y1 : nat, ((dist (@pair nat nat y0 y1)) = (NUMERAL 0)) = (y0 = y1).
Definition term23 (x0 : nat) := fun y0 : nat => ((dist (@pair nat nat x0 y0)) = (NUMERAL 0)) = (x0 = y0).
Definition term19 (x0 : nat) (x1 : nat) := and ((Nat.sub x0 x1) = (NUMERAL 0)).
Definition term30 := forall y0 : nat, forall y1 : nat, ((dist (@pair nat nat y0 y1)) = (NUMERAL 0)) = (y0 = y1).
Definition term17 (x0 : nat) (x1 : nat) := @eq nat (Nat.add (Nat.sub x1 x0) (Nat.sub x0 x1)).
Definition term26 := forall y0 : nat, True.
Definition term24 := fun y0 : nat => True.
Definition term18 (x0 : nat) (x1 : nat) := ((Nat.sub x1 x0) = (NUMERAL 0)) /\ ((Nat.sub x0 x1) = (NUMERAL 0)).
Definition term11 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y1 y0)) = (Nat.add (Nat.sub y1 y0) (Nat.sub y0 y1))) x0.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.add y0 y1) = (NUMERAL 0)) = ((y0 = (NUMERAL 0)) /\ (y1 = (NUMERAL 0)))) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Nat.sub y0 y1) = (NUMERAL 0)) = (Peano.le y0 y1)) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((Peano.le y0 y1) /\ (Peano.le y1 y0)) = (y0 = y1)) x0.
Definition term15 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x1 x0) (Nat.sub x0 x1).
Definition term22 (x0 : nat) (x1 : nat) := @eq Prop (x0 = x1).
Definition term28 (x0 : Prop) := forall y0 : nat, x0.
Definition term12 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0)).
Definition term13 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0))) x1.
Definition term16 (x0 : nat) (x1 : nat) := @eq nat (dist (@pair nat nat x0 x1)).
Definition term20 (x0 : nat) (x1 : nat) := and (Peano.le x0 x1).
Definition term9 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((Nat.add x0 y0) = (NUMERAL 0)) = ((x0 = (NUMERAL 0)) /\ (y0 = (NUMERAL 0)))) x1.
