Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term35 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term15 (x0 : nat) := ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0) -> (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) (S x0).
Definition term33 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (S x0).
Definition term32 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) x0.
Definition term11 (x0 : nat) := imp ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) = (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term27 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term36 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term4 := ~ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0)).
Definition term26 := forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0.
Definition term5 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term7 := and ((~ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))) = (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))).
Definition term21 := ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0) -> (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) (S y0)).
Definition term8 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
Definition term22 := ((~ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))) = (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) /\ (forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (~ (Coq.Arith.PeanoNat.Nat.Odd (S y0))) = (Coq.Arith.PeanoNat.Nat.Even (S y0))).
Definition term16 (x0 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Odd x0)) = (Coq.Arith.PeanoNat.Nat.Even x0)) -> (~ (Coq.Arith.PeanoNat.Nat.Odd (S x0))) = (Coq.Arith.PeanoNat.Nat.Even (S x0)).
Definition term1 := (((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0) -> (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) (S y0))) -> forall y0 : nat, (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0.
Definition term0 (x0 : nat -> Prop) := ((x0 (NUMERAL 0)) /\ (forall y0 : nat, (x0 y0) -> x0 (S y0))) -> forall y0 : nat, x0 y0.
Definition term23 := imp (((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) (NUMERAL 0)) /\ (forall y0 : nat, ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0) -> (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) (S y0))).
Definition term25 := fun y0 : nat => (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0.
Definition term18 := fun y0 : nat => ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (~ (Coq.Arith.PeanoNat.Nat.Odd (S y0))) = (Coq.Arith.PeanoNat.Nat.Even (S y0)).
Definition term19 := forall y0 : nat, ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0) -> (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) (S y0).
Definition term30 := @eq Prop (~ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))).
Definition term6 := and ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) (NUMERAL 0)).
Definition term34 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term31 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term37 (x0 : nat) := @eq Prop (~ (Coq.Arith.PeanoNat.Nat.Odd (S x0))).
Definition term17 := fun y0 : nat => ((fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) y0) -> (fun y1 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y1)) = (Coq.Arith.PeanoNat.Nat.Even y1)) (S y0).
Definition term14 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term2 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term3 := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) (NUMERAL 0).
Definition term38 (x0 : nat) := @eq Prop (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term28 := (((~ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))) = (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) /\ (forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (~ (Coq.Arith.PeanoNat.Nat.Odd (S y0))) = (Coq.Arith.PeanoNat.Nat.Even (S y0)))) -> forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term12 (x0 : nat) := (fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) (S x0).
Definition term29 := Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0).
Definition term9 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term10 (x0 : nat) := imp ((fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0).
Definition term20 := forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (~ (Coq.Arith.PeanoNat.Nat.Odd (S y0))) = (Coq.Arith.PeanoNat.Nat.Even (S y0)).
Definition term13 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd (S x0)).
Definition term24 := imp (((~ (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0))) = (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0))) /\ (forall y0 : nat, ((~ (Coq.Arith.PeanoNat.Nat.Odd y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) -> (~ (Coq.Arith.PeanoNat.Nat.Odd (S y0))) = (Coq.Arith.PeanoNat.Nat.Even (S y0)))).
