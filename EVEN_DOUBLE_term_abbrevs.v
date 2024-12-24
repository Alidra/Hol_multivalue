Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nat) := NUMERAL (BIT0 x0).
Definition term15 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term6 (x0 : nat) := S (Nat.add (NUMERAL x0) (NUMERAL x0)).
Definition term12 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even y0))) x1.
Definition term18 := Nat.add (NUMERAL (BIT1 0)) (NUMERAL (BIT1 0)).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) x1.
Definition term22 := Nat.add (S (Nat.add (NUMERAL 0) (NUMERAL 0))).
Definition term25 := Coq.Arith.PeanoNat.Nat.Even (Nat.add (S (Nat.add (NUMERAL 0) (NUMERAL 0))) (S (Nat.add (NUMERAL 0) (NUMERAL 0)))).
Definition term23 := Nat.add (S (Nat.add (NUMERAL 0) (NUMERAL 0))) (S (Nat.add (NUMERAL 0) (NUMERAL 0))).
Definition term11 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term1 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term20 := S (Nat.add (NUMERAL 0) (NUMERAL 0)).
Definition term4 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT1 y0)) = (S (Nat.add (NUMERAL y0) (NUMERAL y0)))) x0.
Definition term3 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1).
Definition term26 := Coq.Arith.PeanoNat.Nat.Even (S (Nat.add (NUMERAL 0) (NUMERAL 0))).
Definition term7 (x0 : nat) := (fun y0 : nat => (NUMERAL (BIT0 y0)) = (Nat.add (NUMERAL y0) (NUMERAL y0))) x0.
Definition term21 := Nat.add (NUMERAL (BIT1 0)).
Definition term17 := NUMERAL (BIT0 (BIT1 0)).
Definition term10 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.mul y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) \/ (Coq.Arith.PeanoNat.Nat.Even y1))) x0.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) x0.
Definition term14 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) \/ (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term24 := Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT0 (BIT1 0))).
Definition term9 (x0 : nat) := Nat.add (NUMERAL x0) (NUMERAL x0).
Definition term16 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even (NUMERAL (BIT0 (BIT1 0)))) \/ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term13 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul x0 x1).
Definition term27 := forall y0 : nat, Coq.Arith.PeanoNat.Nat.Even (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term5 (x0 : nat) := NUMERAL (BIT1 x0).
Definition term19 := NUMERAL (BIT1 0).
