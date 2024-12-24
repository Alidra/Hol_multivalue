Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term2 (x0 : nat) := (fun y0 : nat => ((Coq.Arith.PeanoNat.Nat.Even y0) -> exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even y0)) -> exists y1 : nat, y0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)))) x0.
Definition term13 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term3 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> exists y0 : nat, x0 = (S (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0))).
Definition term1 (x0 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term16 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) /\ ((exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> Coq.Arith.PeanoNat.Nat.Even x0).
Definition term10 (x0 : nat) := (fun y0 : nat => Coq.Arith.PeanoNat.Nat.Even y0) x0.
Definition term8 (x0 : nat) := Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0.
Definition term15 (x0 : nat) := (exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> Coq.Arith.PeanoNat.Nat.Even x0.
Definition term11 (x0 : nat) := (fun y0 : nat => Coq.Arith.PeanoNat.Nat.Even y0) (Nat.mul (NUMERAL (BIT0 (BIT1 0))) x0).
Definition term9 := fun y0 : nat => Coq.Arith.PeanoNat.Nat.Even y0.
Definition term4 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term5 (x0 : nat) := exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term17 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) = (exists y1 : nat, y0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y1)).
Definition term0 (x0 : nat) := (fun y0 : nat => Coq.Arith.PeanoNat.Nat.Even (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) x0.
Definition term12 (x0 : nat) := @eq Prop ((fun y0 : nat => Coq.Arith.PeanoNat.Nat.Even y0) x0).
Definition term7 (x0 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0)) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> exists y0 : nat, x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
Definition term14 (x0 : nat) := fun y0 : nat => x0 = (Nat.mul (NUMERAL (BIT0 (BIT1 0))) y0).
