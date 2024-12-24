Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term23 := fun y0 : nat => forall y1 : real, forall y2 : real, (((real_lt y1 y2) \/ (y1 = y2)) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) \/ ((real_pow y1 y0) = (real_pow y2 y0)).
Definition term22 := fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term14 (x0 : real) (x1 : nat) := fun y0 : real => ((real_le x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term37 (x0 : real) (x1 : real) (x2 : nat) := True \/ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term26 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_lt y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_lt (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term34 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> (real_lt (real_pow x0 x2) (real_pow x1 x2)) = True.
Definition term11 (x0 : real) (x1 : real) (x2 : nat) := (real_lt (real_pow x0 x2) (real_pow x1 x2)) \/ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term13 (x0 : real) (x1 : real) (x2 : nat) := (((real_lt x0 x1) \/ (x0 = x1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> (real_lt (real_pow x0 x2) (real_pow x1 x2)) \/ ((real_pow x0 x2) = (real_pow x1 x2)).
Definition term6 (x0 : real) (x1 : real) (x2 : nat) := (real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term27 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_lt y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_lt (real_pow y0 x0) (real_pow y1 x0).
Definition term21 (x0 : nat) := forall y0 : real, forall y1 : real, (((real_lt y0 y1) \/ (y0 = y1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> (real_lt (real_pow y0 x0) (real_pow y1 x0)) \/ ((real_pow y0 x0) = (real_pow y1 x0)).
Definition term20 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term29 (x0 : real) (x1 : nat) := forall y0 : real, ((real_lt x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_lt (real_pow x0 x1) (real_pow y0 x1).
Definition term16 (x0 : real) (x1 : nat) := forall y0 : real, ((real_le x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_le (real_pow x0 x1) (real_pow y0 x1).
Definition term10 (x0 : real) (x1 : real) (x2 : nat) := real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term35 (x0 : real) (x1 : real) := and (real_lt x0 x1).
Definition term19 (x0 : nat) := fun y0 : real => forall y1 : real, (((real_lt y0 y1) \/ (y0 = y1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> (real_lt (real_pow y0 x0) (real_pow y1 x0)) \/ ((real_pow y0 x0) = (real_pow y1 x0)).
Definition term18 (x0 : nat) := fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term8 (x0 : real) (x1 : real) (x2 : nat) := imp ((real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term32 (x0 : real) (x1 : real) (x2 : nat) := (real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term25 := forall y0 : nat, forall y1 : real, forall y2 : real, (((real_lt y1 y2) \/ (y1 = y2)) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> (real_lt (real_pow y1 y0) (real_pow y2 y0)) \/ ((real_pow y1 y0) = (real_pow y2 y0)).
Definition term24 := forall y0 : nat, forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0).
Definition term42 (x0 : real) (x1 : nat) := (real_lt (real_pow x0 x1) (real_pow x0 x1)) \/ True.
Definition term36 (x0 : real) (x1 : real) (x2 : nat) := or (real_lt (real_pow x0 x2) (real_pow x1 x2)).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : real, (real_le y0 y1) = ((real_lt y0 y1) \/ (y0 = y1))) x0.
Definition term5 (x0 : real) (x1 : real) := and ((real_lt x0 x1) \/ (x0 = x1)).
Definition term39 (x0 : real) (x1 : nat) := real_lt (real_pow x0 x1) (real_pow x0 x1).
Definition term28 (x0 : nat) (x1 : real) := (fun y0 : real => forall y1 : real, ((real_lt y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_lt (real_pow y0 x0) (real_pow y1 x0)) x1.
Definition term41 (x0 : real) (x1 : nat) := @eq real (real_pow x0 x1).
Definition term33 (x0 : real) (x1 : real) (x2 : nat) := real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term15 (x0 : real) (x1 : nat) := fun y0 : real => (((real_lt x0 y0) \/ (x0 = y0)) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> (real_lt (real_pow x0 x1) (real_pow y0 x1)) \/ ((real_pow x0 x1) = (real_pow y0 x1)).
Definition term3 (x0 : real) (x1 : real) := (real_lt x0 x1) \/ (x0 = x1).
Definition term2 (x0 : real) (x1 : real) := (fun y0 : real => (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0))) x1.
Definition term4 (x0 : real) (x1 : real) := and (real_le x0 x1).
Definition term40 (x0 : real) (x1 : nat) := or (real_lt (real_pow x0 x1) (real_pow x0 x1)).
Definition term12 (x0 : real) (x1 : real) (x2 : nat) := ((real_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> real_le (real_pow x0 x2) (real_pow x1 x2).
Definition term9 (x0 : real) (x1 : real) (x2 : nat) := imp (((real_lt x0 x1) \/ (x0 = x1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term17 (x0 : real) (x1 : nat) := forall y0 : real, (((real_lt x0 y0) \/ (x0 = y0)) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> (real_lt (real_pow x0 x1) (real_pow y0 x1)) \/ ((real_pow x0 x1) = (real_pow y0 x1)).
Definition term1 (x0 : real) := forall y0 : real, (real_le x0 y0) = ((real_lt x0 y0) \/ (x0 = y0)).
Definition term31 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> real_lt (real_pow x0 x2) (real_pow x1 x2).
Definition term7 (x0 : real) (x1 : real) (x2 : nat) := ((real_lt x0 x1) \/ (x0 = x1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term38 (x0 : real) (x1 : nat) := real_lt (real_pow x0 x1).
Definition term30 (x0 : real) (x1 : nat) (x2 : real) := (fun y0 : real => ((real_lt x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_lt (real_pow x0 x1) (real_pow y0 x1)) x2.
