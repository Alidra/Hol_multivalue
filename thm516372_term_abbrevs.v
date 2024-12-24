Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
Definition term40 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False).
Definition term21 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term24 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term31 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True.
Definition term26 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term33 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True).
Definition term37 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x0)).
Definition term14 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term20 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (NUMERAL x0)).
Definition term0 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0).
Definition term32 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True.
Definition term1 := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)).
Definition term22 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term39 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False.
Definition term35 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (BIT1 x0)).
Definition term3 := and ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = True).
Definition term36 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S (Nat.add x0 x0)).
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) x1.
Definition term2 := @eq Prop (Coq.Arith.PeanoNat.Nat.Even 0).
Definition term17 (x0 : nat) := S (Nat.add x0 x0).
Definition term6 := ((Coq.Arith.PeanoNat.Nat.Even (NUMERAL 0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term5 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term15 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term28 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term18 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term13 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (S x0).
Definition term9 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term25 := forall y0 : nat, True.
Definition term4 := and ((Coq.Arith.PeanoNat.Nat.Even 0) = True).
Definition term23 := fun y0 : nat => True.
Definition term11 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1).
Definition term16 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term30 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x0).
Definition term7 := ((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))).
Definition term38 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False.
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) x0.
Definition term29 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (BIT0 x0).
Definition term42 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Even y0)) /\ (((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False))).
Definition term27 (x0 : Prop) := forall y0 : nat, x0.
Definition term19 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (NUMERAL x0).
Definition term34 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (BIT1 x0).
Definition term41 := ((Coq.Arith.PeanoNat.Nat.Even 0) = True) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT0 y0)) = True) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (BIT1 y0)) = False)).
