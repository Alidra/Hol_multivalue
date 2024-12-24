Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term25 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = True.
Definition term21 (x0 : nat) (x1 : nat) (x2 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x1) -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1)) = (Coq.Arith.PeanoNat.Nat.Odd x0)) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1)) = (Coq.Arith.PeanoNat.Nat.Odd x0)) = ((Coq.Arith.PeanoNat.Nat.Even x1) -> x2).
Definition term33 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term0 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term22 (x0 : nat) (x1 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x0 x1)).
Definition term28 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> True.
Definition term26 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x1) -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1)) = (Coq.Arith.PeanoNat.Nat.Odd x0)) = True) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1)) = (Coq.Arith.PeanoNat.Nat.Odd x0)) = ((Coq.Arith.PeanoNat.Nat.Even x1) -> True).
Definition term11 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term19 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = x3) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = (x2 -> x3).
Definition term4 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x0 y0)) = (Coq.Arith.PeanoNat.Nat.Even x0)) x1.
Definition term3 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term23 (x0 : nat) (x1 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1)).
Definition term2 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term36 := forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo y0 y1)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term18 (x0 : nat) (x1 : nat) (x2 : Prop) (x3 : Prop) := (fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = (x2 -> y0)) x3.
Definition term32 := forall y0 : nat, True.
Definition term30 := fun y0 : nat => True.
Definition term24 (x0 : nat) := @eq Prop (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term17 (x0 : nat) (x1 : nat) (x2 : Prop) := forall y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = x2) -> (x2 -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = y0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = (x2 -> y0).
Definition term12 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term20 (x0 : nat) (x1 : nat) (x2 : Prop) := ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x1)) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1)) = (Coq.Arith.PeanoNat.Nat.Odd x0)) = x2) -> ((Coq.Arith.PeanoNat.Nat.Even x1) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1)) = (Coq.Arith.PeanoNat.Nat.Odd x0)) = ((Coq.Arith.PeanoNat.Nat.Even x1) -> x2).
Definition term14 (x0 : nat) (x1 : nat) := forall y0 : Prop, forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = (y0 -> y1).
Definition term13 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term9 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x0 x1).
Definition term29 (x0 : nat) := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 y0)) = (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo y0 y1)) = (Coq.Arith.PeanoNat.Nat.Even y0)) x0.
Definition term1 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term27 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1).
Definition term15 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 x1).
Definition term34 (x0 : Prop) := forall y0 : nat, x0.
Definition term16 (x0 : nat) (x1 : nat) (x2 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Even x0) = y0) -> (y0 -> ((Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = y1) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Odd x1)) = (y0 -> y1)) x2.
Definition term31 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo x0 y0)) = (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term6 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x0 y0)) = (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term35 := fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (Coq.Arith.PeanoNat.Nat.Odd (Nat.modulo y0 y1)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term10 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
