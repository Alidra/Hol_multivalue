Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) (x1 : nat) := and ((real_pow (real_of_num x0) x1) = (real_of_num (Nat.pow x0 x1))).
Definition term19 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.pow x0 x1)).
Definition term23 (x0 : nat) (x1 : nat) := ((real_pow (real_of_num x0) x1) = (real_of_num (Nat.pow x0 x1))) /\ ((real_pow (real_neg (real_of_num x0)) x1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_of_num (Nat.pow x0 x1)) (real_neg (real_of_num (Nat.pow x0 x1))))).
Definition term9 (x0 : nat) (x1 : nat) := real_of_num (Nat.pow x0 x1).
Definition term14 (x0 : nat) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow (real_of_num x0) x1) (real_neg (real_pow (real_of_num x0) x1)).
Definition term17 (x0 : nat) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_of_num (Nat.pow x0 x1)).
Definition term21 (x0 : nat) (x1 : nat) := @eq real (real_pow (real_neg (real_of_num x0)) x1).
Definition term0 (x0 : real) := (fun y0 : real => forall y1 : nat, (real_pow (real_neg y0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow y0 y1) (real_neg (real_pow y0 y1)))) x0.
Definition term18 (x0 : nat) (x1 : nat) := real_neg (real_pow (real_of_num x0) x1).
Definition term7 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0))) x1.
Definition term1 (x0 : real) := forall y0 : nat, (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0))).
Definition term4 (x0 : real) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow x0 x1) (real_neg (real_pow x0 x1)).
Definition term22 (x0 : nat) (x1 : nat) := @eq real (@COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_of_num (Nat.pow x0 x1)) (real_neg (real_of_num (Nat.pow x0 x1)))).
Definition term16 (x0 : nat) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow (real_of_num x0) x1).
Definition term2 (x0 : real) (x1 : nat) := (fun y0 : nat => (real_pow (real_neg x0) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow x0 y0) (real_neg (real_pow x0 y0)))) x1.
Definition term5 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_pow (real_of_num y0) y1) = (real_of_num (Nat.pow y0 y1))) x0.
Definition term3 (x0 : real) (x1 : nat) := real_pow (real_neg x0) x1.
Definition term20 (x0 : nat) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_of_num (Nat.pow x0 x1)) (real_neg (real_of_num (Nat.pow x0 x1))).
Definition term10 (x0 : nat) (x1 : nat) := @eq real (real_pow (real_of_num x0) x1).
Definition term6 (x0 : nat) := forall y0 : nat, (real_pow (real_of_num x0) y0) = (real_of_num (Nat.pow x0 y0)).
Definition term8 (x0 : nat) (x1 : nat) := real_pow (real_of_num x0) x1.
Definition term15 (x0 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term11 (x0 : nat) (x1 : nat) := @eq real (real_of_num (Nat.pow x0 x1)).
Definition term13 (x0 : nat) (x1 : nat) := real_pow (real_neg (real_of_num x0)) x1.
