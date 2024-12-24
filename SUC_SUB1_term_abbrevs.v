Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nat) := Nat.sub (S x0).
Definition term17 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term7 := S (NUMERAL 0).
Definition term3 (x0 : nat) := forall y0 : nat, (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Nat.sub (S x0) (S y0)) = (Nat.sub x0 y0)) x1.
Definition term13 := fun y0 : nat => (Nat.sub (S y0) (NUMERAL (BIT1 0))) = y0.
Definition term9 (x0 : nat) := Nat.sub (S x0) (NUMERAL (BIT1 0)).
Definition term0 (x0 : nat) := (fun y0 : nat => ((Nat.sub (NUMERAL 0) y0) = (NUMERAL 0)) /\ ((Nat.sub y0 (NUMERAL 0)) = y0)) x0.
Definition term15 := forall y0 : nat, (Nat.sub (S y0) (NUMERAL (BIT1 0))) = y0.
Definition term10 (x0 : nat) := Nat.sub (S x0) (S (NUMERAL 0)).
Definition term16 := forall y0 : nat, True.
Definition term14 := fun y0 : nat => True.
Definition term11 (x0 : nat) := Nat.sub x0 (NUMERAL 0).
Definition term5 (x0 : nat) (x1 : nat) := Nat.sub (S x0) (S x1).
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Nat.sub (S y0) (S y1)) = (Nat.sub y0 y1)) x0.
Definition term1 (x0 : nat) := ((Nat.sub (NUMERAL 0) x0) = (NUMERAL 0)) /\ ((Nat.sub x0 (NUMERAL 0)) = x0).
Definition term18 (x0 : Prop) := forall y0 : nat, x0.
Definition term12 (x0 : nat) := @eq nat (Nat.sub (S x0) (NUMERAL (BIT1 0))).
Definition term6 := NUMERAL (BIT1 0).
