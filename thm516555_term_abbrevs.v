Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term43 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True).
Definition term14 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (S x0).
Definition term13 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))) x0.
Definition term6 := ((Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))).
Definition term30 := ~ (Coq.Arith.PeanoNat.Nat.Odd 0).
Definition term27 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term11 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 x1).
Definition term37 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False).
Definition term21 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL x0)).
Definition term1 := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0)).
Definition term42 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True.
Definition term39 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (S (Nat.add x0 x0)).
Definition term38 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (BIT1 x0).
Definition term44 := ((Coq.Arith.PeanoNat.Nat.Odd 0) = False) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True)).
Definition term36 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False.
Definition term10 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 y0)) = (~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd y0)))) x1.
Definition term4 := and ((Coq.Arith.PeanoNat.Nat.Odd 0) = False).
Definition term18 (x0 : nat) := S (Nat.add x0 x0).
Definition term5 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term16 (x0 : nat) := (fun y0 : nat => (BIT0 y0) = (Nat.add y0 y0)) x0.
Definition term29 := and (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0)).
Definition term25 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term19 (x0 : nat) := (fun y0 : nat => (NUMERAL y0) = y0) x0.
Definition term2 := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd 0).
Definition term3 := and ((Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0)) = False).
Definition term45 := (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0)) /\ (((Coq.Arith.PeanoNat.Nat.Odd 0) = False) /\ ((forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True))).
Definition term33 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 x0).
Definition term40 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 x0)).
Definition term26 := forall y0 : nat, True.
Definition term31 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (BIT0 x0).
Definition term24 := fun y0 : nat => True.
Definition term17 (x0 : nat) := (fun y0 : nat => (BIT1 y0) = (S (Nat.add y0 y0))) x0.
Definition term12 (x0 : nat) (x1 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd x1)).
Definition term8 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.add y0 y1)) = (~ ((Coq.Arith.PeanoNat.Nat.Odd y0) = (Coq.Arith.PeanoNat.Nat.Odd y1)))) x0.
Definition term32 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd (BIT0 x0)).
Definition term41 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (BIT1 y0)) = True.
Definition term34 (x0 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd x0)).
Definition term9 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 y0)) = (~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd y0))).
Definition term28 (x0 : Prop) := forall y0 : nat, x0.
Definition term23 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (NUMERAL y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term0 := Coq.Arith.PeanoNat.Nat.Odd (NUMERAL 0).
Definition term15 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term35 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd (BIT0 y0)) = False.
Definition term7 := ((Coq.Arith.PeanoNat.Nat.Odd 0) = False) /\ (forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (S y0)) = (~ (Coq.Arith.PeanoNat.Nat.Odd y0))).
Definition term22 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term20 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Odd (NUMERAL x0).
