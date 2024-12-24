Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term11 (x0 : int) (x1 : int) (x2 : nat) := @eq Prop ((int_pow x0 x2) = (int_pow x1 x2)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : real, forall y2 : real, ((real_pow y1 y0) = (real_pow y2 y0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even y0) ((y0 = (NUMERAL 0)) \/ ((real_abs y1) = (real_abs y2))) (y1 = y2))) x0.
Definition term23 (x0 : nat) (x1 : int) := forall y0 : int, ((int_pow x1 x0) = (int_pow y0 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((int_abs x1) = (int_abs y0))) (x1 = y0)).
Definition term2 (x0 : nat) (x1 : int) := (fun y0 : real => forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs y0) = (real_abs y1))) (y0 = y1))) (real_of_int x1).
Definition term18 (x0 : nat) (x1 : int) (x2 : int) := (x0 = (NUMERAL 0)) \/ ((int_abs x1) = (int_abs x2)).
Definition term1 (x0 : nat) := forall y0 : real, forall y1 : real, ((real_pow y0 x0) = (real_pow y1 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs y0) = (real_abs y1))) (y0 = y1)).
Definition term13 (x0 : int) := real_of_int (int_abs x0).
Definition term14 (x0 : int) := @eq real (real_abs (real_of_int x0)).
Definition term4 (x0 : nat) (x1 : int) (x2 : int) := (fun y0 : real => ((real_pow (real_of_int x1) x0) = (real_pow y0 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_of_int x1)) = (real_abs y0))) ((real_of_int x1) = y0))) (real_of_int x2).
Definition term16 (x0 : nat) := or (x0 = (NUMERAL 0)).
Definition term25 := forall y0 : nat, forall y1 : int, forall y2 : int, ((int_pow y1 y0) = (int_pow y2 y0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even y0) ((y0 = (NUMERAL 0)) \/ ((int_abs y1) = (int_abs y2))) (y1 = y2)).
Definition term24 (x0 : nat) := forall y0 : int, forall y1 : int, ((int_pow y0 x0) = (int_pow y1 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((int_abs y0) = (int_abs y1))) (y0 = y1)).
Definition term3 (x0 : nat) (x1 : int) := forall y0 : real, ((real_pow (real_of_int x1) x0) = (real_pow y0 x0)) = (@COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_of_int x1)) = (real_abs y0))) ((real_of_int x1) = y0)).
Definition term5 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term20 (x0 : nat) (x1 : int) (x2 : int) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_of_int x1)) = (real_abs (real_of_int x2)))).
Definition term17 (x0 : nat) (x1 : int) (x2 : int) := (x0 = (NUMERAL 0)) \/ ((real_abs (real_of_int x1)) = (real_abs (real_of_int x2))).
Definition term8 (x0 : int) (x1 : nat) := @eq real (real_pow (real_of_int x0) x1).
Definition term9 (x0 : int) (x1 : nat) := @eq real (real_of_int (int_pow x0 x1)).
Definition term10 (x0 : int) (x1 : int) (x2 : nat) := @eq Prop ((real_pow (real_of_int x0) x2) = (real_pow (real_of_int x1) x2)).
Definition term19 (x0 : nat) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0).
Definition term21 (x0 : nat) (x1 : int) (x2 : int) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((int_abs x1) = (int_abs x2))).
Definition term12 (x0 : int) := real_abs (real_of_int x0).
Definition term7 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
Definition term6 (x0 : nat) (x1 : int) (x2 : int) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((real_abs (real_of_int x1)) = (real_abs (real_of_int x2)))) ((real_of_int x1) = (real_of_int x2)).
Definition term22 (x0 : nat) (x1 : int) (x2 : int) := @COND Prop (Coq.Arith.PeanoNat.Nat.Even x0) ((x0 = (NUMERAL 0)) \/ ((int_abs x1) = (int_abs x2))) (x1 = x2).
Definition term15 (x0 : int) := @eq real (real_of_int (int_abs x0)).
