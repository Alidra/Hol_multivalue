Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> real_le (real_pow y1 y0) (real_pow y2 y0)) x0.
Definition term15 (x0 : int) (x1 : nat) := real_le (real_pow (real_of_int x0) x1).
Definition term18 (x0 : int) (x1 : int) (x2 : nat) := real_le (real_of_int (int_pow x0 x2)) (real_of_int (int_pow x1 x2)).
Definition term9 (x0 : int) (x1 : int) (x2 : nat) := (real_le (real_of_int x0) (real_of_int x1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term7 (x0 : int) (x1 : int) := and (real_le (real_of_int x0) (real_of_int x1)).
Definition term21 (x0 : int) (x1 : nat) := forall y0 : int, ((int_le x0 y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> int_le (int_pow x0 x1) (int_pow y0 x1).
Definition term2 (x0 : nat) (x1 : int) := (fun y0 : real => forall y1 : real, ((real_le y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_le (real_pow y0 x0) (real_pow y1 x0)) (real_of_int x1).
Definition term1 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_le y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> real_le (real_pow y0 x0) (real_pow y1 x0).
Definition term5 (x0 : int) (x1 : int) (x2 : nat) := ((real_le (real_of_int x0) (real_of_int x1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> real_le (real_pow (real_of_int x0) x2) (real_pow (real_of_int x1) x2).
Definition term3 (x0 : int) (x1 : nat) := forall y0 : real, ((real_le (real_of_int x0) y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_le (real_pow (real_of_int x0) x1) (real_pow y0 x1).
Definition term12 (x0 : int) (x1 : int) (x2 : nat) := imp ((int_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term23 := forall y0 : nat, forall y1 : int, forall y2 : int, ((int_le y1 y2) /\ (Coq.Arith.PeanoNat.Nat.Odd y0)) -> int_le (int_pow y1 y0) (int_pow y2 y0).
Definition term10 (x0 : int) (x1 : int) (x2 : nat) := (int_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2).
Definition term11 (x0 : int) (x1 : int) (x2 : nat) := imp ((real_le (real_of_int x0) (real_of_int x1)) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)).
Definition term22 (x0 : nat) := forall y0 : int, forall y1 : int, ((int_le y0 y1) /\ (Coq.Arith.PeanoNat.Nat.Odd x0)) -> int_le (int_pow y0 x0) (int_pow y1 x0).
Definition term13 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term19 (x0 : int) (x1 : int) (x2 : nat) := int_le (int_pow x0 x2) (int_pow x1 x2).
Definition term6 (x0 : int) (x1 : int) := real_le (real_of_int x0) (real_of_int x1).
Definition term8 (x0 : int) (x1 : int) := and (int_le x0 x1).
Definition term20 (x0 : int) (x1 : int) (x2 : nat) := ((int_le x0 x1) /\ (Coq.Arith.PeanoNat.Nat.Odd x2)) -> int_le (int_pow x0 x2) (int_pow x1 x2).
Definition term14 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term4 (x0 : int) (x1 : nat) (x2 : int) := (fun y0 : real => ((real_le (real_of_int x0) y0) /\ (Coq.Arith.PeanoNat.Nat.Odd x1)) -> real_le (real_pow (real_of_int x0) x1) (real_pow y0 x1)) (real_of_int x2).
Definition term17 (x0 : int) (x1 : int) (x2 : nat) := real_le (real_pow (real_of_int x0) x2) (real_pow (real_of_int x1) x2).
Definition term16 (x0 : int) (x1 : nat) := real_le (real_of_int (int_pow x0 x1)).
