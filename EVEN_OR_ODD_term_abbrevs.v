Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term17 := (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0)).
Definition term26 (x0 : nat) := ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) x0) -> (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) (S x0).
Definition term9 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (S x0).
Definition term8 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) x0.
Definition term33 := ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))) /\ (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> (Coq.Arith.PeanoNat.Nat.Even (S y0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (S y0))).
Definition term20 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) x0.
Definition term6 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term37 := forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0.
Definition term19 := and ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))).
Definition term40 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term32 := ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) (S y0)).
Definition term3 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
Definition term14 := (((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0.
Definition term15 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term13 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term43 (x0 : nat) := or (Coq.Arith.PeanoNat.Nat.Even (S x0)).
Definition term0 (x0 : Prop) := (fun y0 : Prop => forall y1 : Prop, (y0 \/ y1) = (y1 \/ y0)) x0.
Definition term34 := imp (((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) (S y0))).
Definition term30 := forall y0 : nat, ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) (S y0).
Definition term38 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term36 := fun y0 : nat => (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0.
Definition term18 := and ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) (NUMERAL 0)).
Definition term10 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term7 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term23 (x0 : nat) := imp ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term5 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0)) x0.
Definition term28 := fun y0 : nat => ((fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) y0) -> (fun y1 : nat => (Coq.Arith.PeanoNat.Nat.Even y1) \/ (Coq.Arith.PeanoNat.Nat.Odd y1)) (S y0).
Definition term2 (x0 : Prop) (x1 : Prop) := (fun y0 : Prop => (x0 \/ y0) = (y0 \/ x0)) x1.
Definition term12 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term16 := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) (NUMERAL 0).
Definition term39 := (((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))) /\ (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> (Coq.Arith.PeanoNat.Nat.Even (S y0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (S y0)))) -> forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term21 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term27 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> (Coq.Arith.PeanoNat.Nat.Even (S x0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (S x0)).
Definition term41 := or (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)).
Definition term44 (x0 : nat) := or (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term29 := fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> (Coq.Arith.PeanoNat.Nat.Even (S y0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (S y0)).
Definition term42 := Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0).
Definition term25 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even (S x0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (S x0)).
Definition term4 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term22 (x0 : nat) := imp ((fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) x0).
Definition term1 (x0 : Prop) := forall y0 : Prop, (x0 \/ y0) = (y0 \/ x0).
Definition term31 := forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> (Coq.Arith.PeanoNat.Nat.Even (S y0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (S y0)).
Definition term45 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) \/ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term35 := imp (((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))) /\ (forall y0 : nat, ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> (Coq.Arith.PeanoNat.Nat.Even (S y0)) \/ (Coq.Arith.PeanoNat.Nat.Odd (S y0)))).
Definition term24 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Odd y0)) (S x0).
