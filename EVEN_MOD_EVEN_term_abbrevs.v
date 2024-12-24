Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term13 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x1 x0)) = (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term10 (x0 : nat) (x1 : nat) := @eq nat (Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))).
Definition term1 (x0 : nat) := Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))).
Definition term12 (x0 : nat) := @eq Prop ((Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.modulo (Nat.modulo x0 y0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0))))) x1.
Definition term7 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Nat.modulo (Nat.modulo x0 y0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term15 := forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo y0 y1)) = (Coq.Arith.PeanoNat.Nat.Even y0).
Definition term4 (x0 : nat) (x1 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x0 x1)).
Definition term3 (x0 : nat) (x1 : nat) := Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0))).
Definition term5 (x0 : nat) (x1 : nat) := @eq Prop ((Nat.modulo (Nat.modulo x0 x1) (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0)).
Definition term2 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x0 x1).
Definition term6 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (Nat.modulo (Nat.modulo y0 y1) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0))))) x0.
Definition term11 (x0 : nat) := @eq nat (Nat.modulo x0 (NUMERAL (BIT0 (BIT1 0)))).
Definition term14 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (Coq.Arith.PeanoNat.Nat.Even (Nat.modulo x0 y0)) = (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term9 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> (Nat.modulo (Nat.modulo x1 x0) (NUMERAL (BIT0 (BIT1 0)))) = (Nat.modulo x1 (NUMERAL (BIT0 (BIT1 0)))).
Definition term0 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) = ((Nat.modulo y0 (NUMERAL (BIT0 (BIT1 0)))) = (NUMERAL 0))) x0.
