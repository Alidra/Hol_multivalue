Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => (Coq.Arith.PeanoNat.Nat.Even y0) -> (real_pow (real_abs (real_of_int x0)) y0) = (real_pow (real_of_int x0) y0)) x1.
Definition term17 (x0 : int) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x1) -> (int_pow (int_abs x0) x1) = (int_pow x0 x1).
Definition term12 (x0 : int) (x1 : nat) := real_of_int (int_pow (int_abs x0) x1).
Definition term16 (x0 : nat) := imp (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term5 (x0 : int) := real_of_int (int_abs x0).
Definition term13 (x0 : int) (x1 : nat) := @eq real (real_pow (real_abs (real_of_int x0)) x1).
Definition term7 (x0 : int) := real_pow (real_of_int (int_abs x0)).
Definition term15 (x0 : int) (x1 : nat) := int_pow (int_abs x0) x1.
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (real_pow (real_abs y0) y1) = (real_pow y0 y1)) (real_of_int x0).
Definition term6 (x0 : int) := real_pow (real_abs (real_of_int x0)).
Definition term18 (x0 : int) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (int_pow (int_abs x0) y0) = (int_pow x0 y0).
Definition term1 (x0 : int) := forall y0 : nat, (Coq.Arith.PeanoNat.Nat.Even y0) -> (real_pow (real_abs (real_of_int x0)) y0) = (real_pow (real_of_int x0) y0).
Definition term19 := forall y0 : int, forall y1 : nat, (Coq.Arith.PeanoNat.Nat.Even y1) -> (int_pow (int_abs y0) y1) = (int_pow y0 y1).
Definition term10 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term8 (x0 : int) (x1 : nat) := real_pow (real_abs (real_of_int x0)) x1.
Definition term9 (x0 : int) (x1 : nat) := real_pow (real_of_int (int_abs x0)) x1.
Definition term4 (x0 : int) := real_abs (real_of_int x0).
Definition term11 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term3 (x0 : int) (x1 : nat) := (Coq.Arith.PeanoNat.Nat.Even x1) -> (real_pow (real_abs (real_of_int x0)) x1) = (real_pow (real_of_int x0) x1).
Definition term14 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow (int_abs x0) x1)).
