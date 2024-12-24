Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term52 (x0 : nat) := @eq nat (BIT0 (S x0)).
Definition term14 (x0 : nat) := ((fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0) -> (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) (S x0).
Definition term17 := fun y0 : nat => ((BIT0 y0) = (Nat.add y0 y0)) -> (BIT0 (S y0)) = (Nat.add (S y0) (S y0)).
Definition term32 := @eq nat (NUMERAL 0).
Definition term12 (x0 : nat) := BIT0 (S x0).
Definition term34 := (forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))).
Definition term11 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) (S x0).
Definition term25 := forall y0 : nat, (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0.
Definition term20 := ((fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0) -> (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) (S y0)).
Definition term21 := ((BIT0 (NUMERAL 0)) = (Nat.add (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((BIT0 y0) = (Nat.add y0 y0)) -> (BIT0 (S y0)) = (Nat.add (S y0) (S y0))).
Definition term1 := (((fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0) -> (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0.
Definition term47 (x0 : nat) := (fun y0 : nat => (BIT0 (S y0)) = (S (S (BIT0 y0)))) x0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term43 (x0 : nat) := forall y0 : nat, (Nat.add (S x0) y0) = (S (Nat.add x0 y0)).
Definition term55 (x0 : nat) := Nat.add x0 (S x0).
Definition term22 := imp (((fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0) -> (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) (S y0))).
Definition term18 := forall y0 : nat, ((fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0) -> (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) (S y0).
Definition term46 := forall y0 : nat, (BIT0 (S y0)) = (S (S (BIT0 y0))).
Definition term53 (x0 : nat) := @eq nat (S (S (Nat.add x0 x0))).
Definition term50 (x0 : nat) := S (Nat.add x0 x0).
Definition term6 := and ((fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) (NUMERAL 0)).
Definition term5 := Nat.add (NUMERAL 0) (NUMERAL 0).
Definition term26 := forall y0 : nat, (BIT0 y0) = (Nat.add y0 y0).
Definition term8 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term44 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add (S x0) y0) = (S (Nat.add x0 y0))) x1.
Definition term13 (x0 : nat) := Nat.add (S x0) (S x0).
Definition term16 := fun y0 : nat => ((fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0) -> (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) (S y0).
Definition term30 (x0 : nat) := Nat.add (NUMERAL 0) x0.
Definition term40 (x0 : nat) (x1 : nat) := S (Nat.add x0 x1).
Definition term41 := forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1)).
Definition term35 := forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)).
Definition term4 := BIT0 (NUMERAL 0).
Definition term10 (x0 : nat) := imp ((BIT0 x0) = (Nat.add x0 x0)).
Definition term28 := forall y0 : nat, (Nat.add (NUMERAL 0) y0) = y0.
Definition term29 (x0 : nat) := (fun y0 : nat => (Nat.add (NUMERAL 0) y0) = y0) x0.
Definition term7 := and ((BIT0 (NUMERAL 0)) = (Nat.add (NUMERAL 0) (NUMERAL 0))).
Definition term27 := (((BIT0 (NUMERAL 0)) = (Nat.add (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((BIT0 y0) = (Nat.add y0 y0)) -> (BIT0 (S y0)) = (Nat.add (S y0) (S y0)))) -> forall y0 : nat, (BIT0 y0) = (Nat.add y0 y0).
Definition term2 := fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0).
Definition term38 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.add x0 (S y0)) = (S (Nat.add x0 y0))) x1.
Definition term33 := (forall y0 : nat, (Nat.add y0 (NUMERAL 0)) = y0) /\ ((forall y0 : nat, forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1)))).
Definition term48 (x0 : nat) := S (S (BIT0 x0)).
Definition term42 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add (S y0) y1) = (S (Nat.add y0 y1))) x0.
Definition term36 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.add y0 (S y1)) = (S (Nat.add y0 y1))) x0.
Definition term39 (x0 : nat) (x1 : nat) := Nat.add x0 (S x1).
Definition term23 := imp (((BIT0 (NUMERAL 0)) = (Nat.add (NUMERAL 0) (NUMERAL 0))) /\ (forall y0 : nat, ((BIT0 y0) = (Nat.add y0 y0)) -> (BIT0 (S y0)) = (Nat.add (S y0) (S y0)))).
Definition term24 := fun y0 : nat => (fun y1 : nat => (BIT0 y1) = (Nat.add y1 y1)) y0.
Definition term19 := forall y0 : nat, ((BIT0 y0) = (Nat.add y0 y0)) -> (BIT0 (S y0)) = (Nat.add (S y0) (S y0)).
Definition term49 (x0 : nat) := S (BIT0 x0).
Definition term54 (x0 : nat) := S (Nat.add x0 (S x0)).
Definition term9 (x0 : nat) := imp ((fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0).
Definition term15 (x0 : nat) := ((BIT0 x0) = (Nat.add x0 x0)) -> (BIT0 (S x0)) = (Nat.add (S x0) (S x0)).
Definition term31 := @eq nat (BIT0 (NUMERAL 0)).
Definition term45 (x0 : nat) (x1 : nat) := Nat.add (S x0) x1.
Definition term51 (x0 : nat) := S (S (Nat.add x0 x0)).
Definition term3 := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) (NUMERAL 0).
Definition term37 (x0 : nat) := forall y0 : nat, (Nat.add x0 (S y0)) = (S (Nat.add x0 y0)).
