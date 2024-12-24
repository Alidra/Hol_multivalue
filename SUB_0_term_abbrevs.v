Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 (x0 : nat) := ((fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) x0) -> (fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) (S x0).
Definition term41 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0))) x1.
Definition term43 (x0 : nat) (x1 : nat) := Nat.pred (Nat.sub x0 x1).
Definition term6 (x0 : nat) := ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) /\ True.
Definition term14 := (fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) (NUMERAL 0).
Definition term37 := @eq nat (NUMERAL 0).
Definition term11 := forall y0 : nat, (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0).
Definition term17 := and ((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)).
Definition term42 (x0 : nat) (x1 : nat) := Nat.sub x0 (S x1).
Definition term22 (x0 : nat) := Nat.sub (NUMERAL 0) (S x0).
Definition term3 (x0 : nat) := @eq nat (Nat.sub x0 (NUMERAL 0)).
Definition term18 (x0 : nat) := (fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) x0.
Definition term34 := forall y0 : nat, (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0.
Definition term29 := ((fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) (S y0)).
Definition term32 := imp (((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) -> (Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0))).
Definition term1 (x0 : nat) := (fun y0 : nat => (Nat.sub y0 (NUMERAL 0)) = y0) x0.
Definition term40 (x0 : nat) := forall y0 : nat, (Nat.sub x0 (S y0)) = (Nat.pred (Nat.sub x0 y0)).
Definition term13 := (((fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0.
Definition term12 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term4 (x0 : nat) := and ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)).
Definition term31 := imp (((fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) (S y0))).
Definition term27 := forall y0 : nat, ((fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) (S y0).
Definition term30 := ((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) -> (Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0)).
Definition term26 := fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) -> (Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0).
Definition term0 := forall y0 : nat, (Nat.sub y0 (NUMERAL 0)) = y0.
Definition term7 (x0 : nat) := Nat.sub (NUMERAL 0) x0.
Definition term16 := and ((fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) (NUMERAL 0)).
Definition term21 (x0 : nat) := (fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) (S x0).
Definition term25 := fun y0 : nat => ((fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0) -> (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) (S y0).
Definition term28 := forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) -> (Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0).
Definition term38 := forall y0 : nat, forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1)).
Definition term2 (x0 : nat) := Nat.sub x0 (NUMERAL 0).
Definition term8 := fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((Nat.sub y0 (NUMERAL 0)) = y0).
Definition term39 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub y0 (S y1)) = (Nat.pred (Nat.sub y0 y1))) x0.
Definition term5 (x0 : nat) := ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) /\ ((Nat.sub x0 (NUMERAL 0)) = x0).
Definition term10 := forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((Nat.sub y0 (NUMERAL 0)) = y0).
Definition term45 := Nat.pred (NUMERAL 0).
Definition term44 (x0 : nat) := Nat.pred (Nat.sub (NUMERAL 0) x0).
Definition term36 := @eq nat (Nat.sub (NUMERAL 0) (NUMERAL 0)).
Definition term33 := fun y0 : nat => (fun y1 : nat => (Nat.sub (NUMERAL 0) y1) = (NUMERAL 0)) y0.
Definition term46 (x0 : nat) := @eq nat (Nat.sub (NUMERAL 0) (S x0)).
Definition term20 (x0 : nat) := imp ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)).
Definition term15 := Nat.sub (NUMERAL 0) (NUMERAL 0).
Definition term19 (x0 : nat) := imp ((fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) x0).
Definition term35 := (((Nat.sub (NUMERAL 0) (NUMERAL 0)) = (NUMERAL 0)) /\ (forall y0 : nat, ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) -> (Nat.sub (NUMERAL 0) (S y0)) = (NUMERAL 0))) -> forall y0 : nat, (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0).
Definition term24 (x0 : nat) := ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) -> (Nat.sub (NUMERAL 0) (S x0)) = (NUMERAL 0).
Definition term9 := fun y0 : nat => (Nat.sub (NUMERAL 0) y0) = (NUMERAL 0).
