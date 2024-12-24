Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term25 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term15 (x0 : nat) (x1 : nat) := dist (@pair nat nat x0 x1).
Definition term2 (x0 : nat) := (fun y0 : nat => (Nat.add y0 (NUMERAL 0)) = y0) x0.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (Nat.add y0 y1) y0) = y1) x0.
Definition term3 (x0 : nat) := Nat.add x0 (NUMERAL 0).
Definition term20 (x0 : nat) (x1 : nat) := @eq nat (dist (@pair nat nat (Nat.add x1 x0) x1)).
Definition term1 := forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0.
Definition term11 (x0 : nat) (x1 : nat) := Nat.sub (Nat.add x1 x0) x1.
Definition term28 := forall y0 : nat, forall y1 : nat, (dist (@pair nat nat (Nat.add y0 y1) y0)) = y1.
Definition term24 := forall y0 : nat, True.
Definition term9 (x0 : nat) := forall y0 : nat, (Nat.sub (Nat.add x0 y0) x0) = y0.
Definition term6 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0)) x1.
Definition term22 := fun y0 : nat => True.
Definition term17 (x0 : nat) (x1 : nat) := dist (@pair nat nat (Nat.add x1 x0) x1).
Definition term18 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.add x0 x1) x0) (Nat.sub x0 (Nat.add x0 x1)).
Definition term0 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term23 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat (Nat.add x0 y0) x0)) = y0.
Definition term7 (x0 : nat) (x1 : nat) := Nat.sub x0 (Nat.add x0 x1).
Definition term12 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (dist (@pair nat nat y1 y0)) = (Nat.add (Nat.sub y1 y0) (Nat.sub y0 y1))) x0.
Definition term4 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub y0 (Nat.add y0 y1)) = (NUMERAL 0)) x0.
Definition term5 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (Nat.add x0 y0)) = (NUMERAL 0).
Definition term16 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub x1 x0) (Nat.sub x0 x1).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (Nat.add x0 y0) x0) = y0) x1.
Definition term26 (x0 : Prop) := forall y0 : nat, x0.
Definition term13 (x0 : nat) := forall y0 : nat, (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0)).
Definition term27 := fun y0 : nat => forall y1 : nat, (dist (@pair nat nat (Nat.add y0 y1) y0)) = y1.
Definition term14 (x0 : nat) (x1 : nat) := (fun y0 : nat => (dist (@pair nat nat y0 x0)) = (Nat.add (Nat.sub y0 x0) (Nat.sub x0 y0))) x1.
Definition term21 (x0 : nat) := fun y0 : nat => (dist (@pair nat nat (Nat.add x0 y0) x0)) = y0.
Definition term19 (x0 : nat) (x1 : nat) := Nat.add (Nat.sub (Nat.add x1 x0) x1).
