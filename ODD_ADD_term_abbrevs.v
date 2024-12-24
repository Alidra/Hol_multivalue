Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term36 (x0 : nat) (x1 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x0)) /\ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term22 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 -> False) ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term10 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 x1).
Definition term35 (x0 : nat) (x1 : nat) := @eq Prop (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))).
Definition term0 (x0 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term11 (x0 : nat) (x1 : nat) := ~ (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1)).
Definition term28 (x0 : nat) (x1 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x1)) -> False.
Definition term12 (x0 : nat) (x1 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term32 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x1) = (Coq.Arith.PeanoNat.Nat.Even x0)) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> Coq.Arith.PeanoNat.Nat.Even x1.
Definition term38 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x1) -> Coq.Arith.PeanoNat.Nat.Even x0) -> ((Coq.Arith.PeanoNat.Nat.Even x0) -> Coq.Arith.PeanoNat.Nat.Even x1) -> False.
Definition term18 (x0 : nat) (x1 : nat) := ~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term14 (x0 : nat) (x1 : nat) := @eq Prop (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term34 (x0 : nat) (x1 : nat) := (fun y0 : Prop => y0 -> False) ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0))) x1.
Definition term26 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> False.
Definition term4 := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term3 := forall y0 : nat, (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term33 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)) -> (Coq.Arith.PeanoNat.Nat.Even x0) -> Coq.Arith.PeanoNat.Nat.Even x1.
Definition term21 (x0 : nat) (x1 : nat) := (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term2 := fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term42 := forall y0 : nat, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.add y0 y1)) = (~ ((Coq.Arith.PeanoNat.Nat.Odd y0) = (Coq.Arith.PeanoNat.Nat.Odd y1))).
Definition term6 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 y0)) = ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even y0)).
Definition term31 (x0 : nat) (x1 : nat) := (~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))) -> ~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term29 (x0 : nat) (x1 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x1)) -> False.
Definition term16 (x0 : nat) := @eq Prop (~ (Coq.Arith.PeanoNat.Nat.Even x0)).
Definition term8 (x0 : nat) (x1 : nat) := Coq.Arith.PeanoNat.Nat.Even (Nat.add x0 x1).
Definition term27 (x0 : nat) := (fun y0 : Prop => y0 -> False) (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term20 (x0 : nat) (x1 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))) -> (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term19 (x0 : nat) (x1 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x1)) = (~ (Coq.Arith.PeanoNat.Nat.Even x0))) -> (~ (Coq.Arith.PeanoNat.Nat.Even x0)) -> ~ (Coq.Arith.PeanoNat.Nat.Even x1).
Definition term17 (x0 : nat) (x1 : nat) := ~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd x1)).
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even (Nat.add y0 y1)) = ((Coq.Arith.PeanoNat.Nat.Even y0) = (Coq.Arith.PeanoNat.Nat.Even y1))) x0.
Definition term39 (x0 : nat) (x1 : nat) := (~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))) -> ~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)).
Definition term1 := fun y0 : nat => (~ (Coq.Arith.PeanoNat.Nat.Even y0)) = (Coq.Arith.PeanoNat.Nat.Odd y0).
Definition term41 (x0 : nat) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 y0)) = (~ ((Coq.Arith.PeanoNat.Nat.Odd x0) = (Coq.Arith.PeanoNat.Nat.Odd y0))).
Definition term13 (x0 : nat) (x1 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd (Nat.add x0 x1)).
Definition term30 (x0 : nat) (x1 : nat) := ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1))) -> False.
Definition term24 (x0 : nat) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x0) -> Coq.Arith.PeanoNat.Nat.Even x1.
Definition term37 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) -> Coq.Arith.PeanoNat.Nat.Even x1) -> False.
Definition term40 (x0 : nat) (x1 : nat) := ((~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))) -> ~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))) /\ ((~ ((~ (Coq.Arith.PeanoNat.Nat.Even x0)) = (~ (Coq.Arith.PeanoNat.Nat.Even x1)))) -> ~ ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1))).
Definition term25 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x1) -> Coq.Arith.PeanoNat.Nat.Even x0) /\ ((Coq.Arith.PeanoNat.Nat.Even x0) -> Coq.Arith.PeanoNat.Nat.Even x1).
Definition term23 (x0 : nat) (x1 : nat) := ((Coq.Arith.PeanoNat.Nat.Even x0) = (Coq.Arith.PeanoNat.Nat.Even x1)) -> False.
Definition term15 (x0 : nat) := @eq Prop (Coq.Arith.PeanoNat.Nat.Odd x0).
Definition term9 (x0 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Odd y0) = (~ (Coq.Arith.PeanoNat.Nat.Even y0))) x0.
