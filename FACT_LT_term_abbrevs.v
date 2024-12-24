Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term15 (x0 : nat) := ((fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) x0) -> (fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) (S x0).
Definition term1 (x0 : nat) := Peano.lt (NUMERAL 0) (S x0).
Definition term6 := Peano.lt (NUMERAL 0) (Factorial.fact (NUMERAL 0)).
Definition term39 (x0 : nat) := (fun y0 : nat => (Factorial.fact (S y0)) = (Nat.mul (S y0) (Factorial.fact y0))) x0.
Definition term25 := fun y0 : nat => (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0.
Definition term46 := S (NUMERAL 0).
Definition term22 := (Peano.lt (NUMERAL 0) (Factorial.fact (NUMERAL 0))) /\ (forall y0 : nat, (Peano.lt (NUMERAL 0) (Factorial.fact y0)) -> Peano.lt (NUMERAL 0) (Factorial.fact (S y0))).
Definition term26 := forall y0 : nat, (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0.
Definition term21 := ((fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0) -> (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) (S y0)).
Definition term3 := (((fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0) -> (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0.
Definition term2 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term32 := Peano.lt (NUMERAL 0) (NUMERAL (BIT1 0)).
Definition term35 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Peano.lt (NUMERAL 0) (Nat.mul x0 y0)) = ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt (NUMERAL 0) y0))) x1.
Definition term10 (x0 : nat) := Peano.lt (NUMERAL 0) (Factorial.fact x0).
Definition term23 := imp (((fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0) -> (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) (S y0))).
Definition term43 (x0 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ (Peano.lt (NUMERAL 0) (Factorial.fact x0)).
Definition term19 := forall y0 : nat, ((fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0) -> (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) (S y0).
Definition term5 := (fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) (NUMERAL 0).
Definition term45 (x0 : nat) := (Peano.lt (NUMERAL 0) (S x0)) /\ True.
Definition term7 := and ((fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) (NUMERAL 0)).
Definition term47 := Peano.lt (NUMERAL 0) (S (NUMERAL 0)).
Definition term17 := fun y0 : nat => ((fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) y0) -> (fun y1 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y1)) (S y0).
Definition term37 (x0 : nat) (x1 : nat) := (Peano.lt (NUMERAL 0) x0) /\ (Peano.lt (NUMERAL 0) x1).
Definition term31 := Peano.lt (NUMERAL 0).
Definition term38 := forall y0 : nat, (Factorial.fact (S y0)) = (Nat.mul (S y0) (Factorial.fact y0)).
Definition term27 := forall y0 : nat, Peano.lt (NUMERAL 0) (Factorial.fact y0).
Definition term34 (x0 : nat) := forall y0 : nat, (Peano.lt (NUMERAL 0) (Nat.mul x0 y0)) = ((Peano.lt (NUMERAL 0) x0) /\ (Peano.lt (NUMERAL 0) y0)).
Definition term14 (x0 : nat) := Peano.lt (NUMERAL 0) (Factorial.fact (S x0)).
Definition term28 := ((Peano.lt (NUMERAL 0) (Factorial.fact (NUMERAL 0))) /\ (forall y0 : nat, (Peano.lt (NUMERAL 0) (Factorial.fact y0)) -> Peano.lt (NUMERAL 0) (Factorial.fact (S y0)))) -> forall y0 : nat, Peano.lt (NUMERAL 0) (Factorial.fact y0).
Definition term8 := and (Peano.lt (NUMERAL 0) (Factorial.fact (NUMERAL 0))).
Definition term33 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Peano.lt (NUMERAL 0) (Nat.mul y0 y1)) = ((Peano.lt (NUMERAL 0) y0) /\ (Peano.lt (NUMERAL 0) y1))) x0.
Definition term42 (x0 : nat) := Peano.lt (NUMERAL 0) (Nat.mul (S x0) (Factorial.fact x0)).
Definition term16 (x0 : nat) := (Peano.lt (NUMERAL 0) (Factorial.fact x0)) -> Peano.lt (NUMERAL 0) (Factorial.fact (S x0)).
Definition term44 (x0 : nat) := and (Peano.lt (NUMERAL 0) (S x0)).
Definition term36 (x0 : nat) (x1 : nat) := Peano.lt (NUMERAL 0) (Nat.mul x0 x1).
Definition term18 := fun y0 : nat => (Peano.lt (NUMERAL 0) (Factorial.fact y0)) -> Peano.lt (NUMERAL 0) (Factorial.fact (S y0)).
Definition term4 := fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0).
Definition term29 := Factorial.fact (NUMERAL 0).
Definition term41 (x0 : nat) := Nat.mul (S x0) (Factorial.fact x0).
Definition term11 (x0 : nat) := imp ((fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) x0).
Definition term20 := forall y0 : nat, (Peano.lt (NUMERAL 0) (Factorial.fact y0)) -> Peano.lt (NUMERAL 0) (Factorial.fact (S y0)).
Definition term9 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) x0.
Definition term40 (x0 : nat) := Factorial.fact (S x0).
Definition term30 := NUMERAL (BIT1 0).
Definition term13 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (Factorial.fact y0)) (S x0).
Definition term12 (x0 : nat) := imp (Peano.lt (NUMERAL 0) (Factorial.fact x0)).
Definition term24 := imp ((Peano.lt (NUMERAL 0) (Factorial.fact (NUMERAL 0))) /\ (forall y0 : nat, (Peano.lt (NUMERAL 0) (Factorial.fact y0)) -> Peano.lt (NUMERAL 0) (Factorial.fact (S y0)))).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.lt (NUMERAL 0) (S y0)) x0.
