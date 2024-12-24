Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term3 (x0 : real) := forall y0 : real, ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term2 (x0 : real) := fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term45 := fun y0 : nat => forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2).
Definition term13 (x0 : nat) (x1 : real) (x2 : real) := (fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_pow x1 x0) (real_pow y0 x0)) = (real_le x1 y0)) x2.
Definition term36 (x0 : nat) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> True.
Definition term9 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> (real_le (real_pow y1 y0) (real_pow y2 y0)) = (real_le y1 y2)) x0.
Definition term41 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term38 := fun y0 : real => True.
Definition term17 (x0 : real) (x1 : real) := (fun y0 : real => (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0))) x1.
Definition term31 (x0 : real) (x1 : real) (x2 : nat) := @eq Prop ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term35 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2).
Definition term14 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_pow x1 x0) (real_pow x2 x0)) = (real_le x1 x2).
Definition term40 := forall y0 : real, True.
Definition term42 (x0 : Prop) := forall y0 : real, x0.
Definition term44 (x0 : nat) := forall y0 : real, forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow y0 x0) = (real_pow y1 x0)) = (y0 = y1).
Definition term10 (x0 : nat) := forall y0 : real, forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_pow y0 x0) (real_pow y1 x0)) = (real_le y0 y1).
Definition term8 := forall y0 : real, forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term7 := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term22 (x0 : nat) (x1 : real) (x2 : real) (x3 : Prop) := (fun y0 : Prop => forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Odd x0) = y0) -> (y0 -> (((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = y1) -> ((Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = (y0 -> y1)) x3.
Definition term34 (x0 : real) (x1 : real) (x2 : nat) := ((Coq.Arith.PeanoNat.Nat.Odd x2) -> (((real_pow x0 x2) = (real_pow x1 x2)) = (x0 = x1)) = True) -> ((Coq.Arith.PeanoNat.Nat.Odd x2) -> ((real_pow x0 x2) = (real_pow x1 x2)) = (x0 = x1)) = ((Coq.Arith.PeanoNat.Nat.Odd x2) -> True).
Definition term25 (x0 : nat) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := ((Coq.Arith.PeanoNat.Nat.Odd x0) = x3) -> (x3 -> (((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = x4) -> ((Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = (x3 -> x4).
Definition term15 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term18 (x0 : Prop) (x1 : Prop) (x2 : Prop) (x3 : Prop) := (x0 = x2) -> (x2 -> x1 = x3) -> (x0 -> x1) = (x2 -> x3).
Definition term27 (x0 : real) (x1 : real) (x2 : nat) (x3 : Prop) := ((Coq.Arith.PeanoNat.Nat.Odd x2) -> (((real_pow x0 x2) = (real_pow x1 x2)) = (x0 = x1)) = x3) -> ((Coq.Arith.PeanoNat.Nat.Odd x2) -> ((real_pow x0 x2) = (real_pow x1 x2)) = (x0 = x1)) = ((Coq.Arith.PeanoNat.Nat.Odd x2) -> x3).
Definition term43 (x0 : nat) := fun y0 : real => forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow y0 x0) = (real_pow y1 x0)) = (y0 = y1).
Definition term6 := fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0)).
Definition term0 (x0 : real) (x1 : real) := (real_le x1 x0) /\ (real_le x0 x1).
Definition term26 (x0 : real) (x1 : real) (x2 : nat) (x3 : Prop) := ((Coq.Arith.PeanoNat.Nat.Odd x2) = (Coq.Arith.PeanoNat.Nat.Odd x2)) -> ((Coq.Arith.PeanoNat.Nat.Odd x2) -> (((real_pow x0 x2) = (real_pow x1 x2)) = (x0 = x1)) = x3) -> ((Coq.Arith.PeanoNat.Nat.Odd x2) -> ((real_pow x0 x2) = (real_pow x1 x2)) = (x0 = x1)) = ((Coq.Arith.PeanoNat.Nat.Odd x2) -> x3).
Definition term47 := forall y0 : nat, forall y1 : real, forall y2 : real, (Coq.Arith.PeanoNat.Nat.Odd y0) -> ((real_pow y1 y0) = (real_pow y2 y0)) = (y1 = y2).
Definition term48 := forall y0 : nat, True.
Definition term5 := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (real_le y1 y0)) = (y0 = y1).
Definition term16 (x0 : real) := (fun y0 : real => forall y1 : real, (y0 = y1) = ((real_le y0 y1) /\ (real_le y1 y0))) x0.
Definition term46 := fun y0 : nat => True.
Definition term23 (x0 : nat) (x1 : real) (x2 : real) (x3 : Prop) := forall y0 : Prop, ((Coq.Arith.PeanoNat.Nat.Odd x0) = x3) -> (x3 -> (((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = y0) -> ((Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = (x3 -> y0).
Definition term19 (x0 : Prop) (x1 : Prop) (x2 : Prop) := forall y0 : Prop, (x0 = x2) -> (x2 -> x1 = y0) -> (x0 -> x1) = (x2 -> y0).
Definition term33 (x0 : nat) (x1 : real) (x2 : real) := (Coq.Arith.PeanoNat.Nat.Odd x0) -> (((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = True.
Definition term1 (x0 : real) := fun y0 : real => ((real_le x0 y0) /\ (real_le y0 x0)) = (x0 = y0).
Definition term21 (x0 : nat) (x1 : real) (x2 : real) := forall y0 : Prop, forall y1 : Prop, ((Coq.Arith.PeanoNat.Nat.Odd x0) = y0) -> (y0 -> (((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = y1) -> ((Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = (y0 -> y1).
Definition term20 (x0 : Prop) (x1 : Prop) := forall y0 : Prop, forall y1 : Prop, (x0 = y0) -> (y0 -> x1 = y1) -> (x0 -> x1) = (y0 -> y1).
Definition term11 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_pow y0 x0) (real_pow y1 x0)) = (real_le y0 y1)) x1.
Definition term24 (x0 : nat) (x1 : real) (x2 : real) (x3 : Prop) (x4 : Prop) := (fun y0 : Prop => ((Coq.Arith.PeanoNat.Nat.Odd x0) = x3) -> (x3 -> (((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = y0) -> ((Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow x2 x0)) = (x1 = x2)) = (x3 -> y0)) x4.
Definition term30 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term49 (x0 : Prop) := forall y0 : nat, x0.
Definition term37 (x0 : nat) (x1 : real) := fun y0 : real => (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow y0 x0)) = (x1 = y0).
Definition term39 (x0 : nat) (x1 : real) := forall y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> ((real_pow x1 x0) = (real_pow y0 x0)) = (x1 = y0).
Definition term12 (x0 : nat) (x1 : real) := forall y0 : real, (Coq.Arith.PeanoNat.Nat.Odd x0) -> (real_le (real_pow x1 x0) (real_pow y0 x0)) = (real_le x1 y0).
Definition term4 (x0 : real) := forall y0 : real, (x0 = y0) = ((real_le x0 y0) /\ (real_le y0 x0)).
Definition term32 (x0 : real) (x1 : real) := @eq Prop ((real_le x1 x0) /\ (real_le x0 x1)).
Definition term29 (x0 : real) (x1 : real) (x2 : nat) := and (real_le (real_pow x0 x2) (real_pow x1 x2)).
Definition term28 (x0 : real) (x1 : real) (x2 : nat) := (real_le (real_pow x1 x2) (real_pow x0 x2)) /\ (real_le (real_pow x0 x2) (real_pow x1 x2)).
