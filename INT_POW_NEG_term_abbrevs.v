Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term17 (x0 : int) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_of_int (int_pow x0 x1)).
Definition term26 (x0 : int) (x1 : nat) := int_pow (int_neg x0) x1.
Definition term12 (x0 : int) (x1 : nat) := real_of_int (int_pow (int_neg x0) x1).
Definition term23 (x0 : Prop) (x1 : int) (x2 : int) := real_of_int (@COND int x0 x1 x2).
Definition term4 (x0 : int) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow (real_of_int x0) x1) (real_neg (real_pow (real_of_int x0) x1)).
Definition term13 (x0 : int) (x1 : nat) := @eq real (real_pow (real_neg (real_of_int x0)) x1).
Definition term0 (x0 : int) := (fun y0 : real => forall y1 : nat, (real_pow (real_neg y0) y1) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y1) (real_pow y0 y1) (real_neg (real_pow y0 y1)))) (real_of_int x0).
Definition term21 (x0 : int) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_of_int (int_pow x0 x1)) (real_of_int (int_neg (int_pow x0 x1))).
Definition term18 (x0 : int) (x1 : nat) := real_neg (real_pow (real_of_int x0) x1).
Definition term28 (x0 : int) := forall y0 : nat, (int_pow (int_neg x0) y0) = (@COND int (Coq.Arith.PeanoNat.Nat.Even y0) (int_pow x0 y0) (int_neg (int_pow x0 y0))).
Definition term1 (x0 : int) := forall y0 : nat, (real_pow (real_neg (real_of_int x0)) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow (real_of_int x0) y0) (real_neg (real_pow (real_of_int x0) y0))).
Definition term9 (x0 : int) (x1 : nat) := real_pow (real_of_int (int_neg x0)) x1.
Definition term19 (x0 : int) (x1 : nat) := real_neg (real_of_int (int_pow x0 x1)).
Definition term29 := forall y0 : int, forall y1 : nat, (int_pow (int_neg y0) y1) = (@COND int (Coq.Arith.PeanoNat.Nat.Even y1) (int_pow y0 y1) (int_neg (int_pow y0 y1))).
Definition term20 (x0 : int) (x1 : nat) := real_of_int (int_neg (int_pow x0 x1)).
Definition term10 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term16 (x0 : int) (x1 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x1) (real_pow (real_of_int x0) x1).
Definition term25 (x0 : int) (x1 : nat) := int_neg (int_pow x0 x1).
Definition term3 (x0 : int) (x1 : nat) := real_pow (real_neg (real_of_int x0)) x1.
Definition term5 (x0 : int) := real_neg (real_of_int x0).
Definition term2 (x0 : int) (x1 : nat) := (fun y0 : nat => (real_pow (real_neg (real_of_int x0)) y0) = (@COND real (Coq.Arith.PeanoNat.Nat.Even y0) (real_pow (real_of_int x0) y0) (real_neg (real_pow (real_of_int x0) y0)))) x1.
Definition term8 (x0 : int) := real_pow (real_of_int (int_neg x0)).
Definition term22 (x0 : Prop) (x1 : int) (x2 : int) := @COND real x0 (real_of_int x1) (real_of_int x2).
Definition term7 (x0 : int) := real_pow (real_neg (real_of_int x0)).
Definition term6 (x0 : int) := real_of_int (int_neg x0).
Definition term15 (x0 : nat) := @COND real (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term24 (x0 : int) (x1 : nat) := real_of_int (@COND int (Coq.Arith.PeanoNat.Nat.Even x1) (int_pow x0 x1) (int_neg (int_pow x0 x1))).
Definition term27 (x0 : int) (x1 : nat) := @COND int (Coq.Arith.PeanoNat.Nat.Even x1) (int_pow x0 x1) (int_neg (int_pow x0 x1)).
Definition term11 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term14 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow (int_neg x0) x1)).
