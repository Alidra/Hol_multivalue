Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term20 (x0 : nat) (x1 : nat) := real_neg (real_of_int (int_of_num (Nat.sub x0 x1))).
Definition term10 (x0 : int) (x1 : int) := real_of_int (int_sub x0 x1).
Definition term9 (x0 : int) (x1 : int) := real_sub (real_of_int x0) (real_of_int x1).
Definition term13 (x0 : nat) (x1 : nat) := @eq real (real_of_int (int_sub (int_of_num x0) (int_of_num x1))).
Definition term25 (x0 : nat) (x1 : nat) := @COND real (Peano.le x0 x1) (real_of_int (int_of_num (Nat.sub x1 x0))) (real_of_int (int_neg (int_of_num (Nat.sub x0 x1)))).
Definition term14 (x0 : nat) (x1 : nat) := real_of_num (Nat.sub x0 x1).
Definition term27 (x0 : Prop) (x1 : int) (x2 : int) := real_of_int (@COND int x0 x1 x2).
Definition term3 (x0 : nat) (x1 : nat) := real_sub (real_of_num x0) (real_of_num x1).
Definition term12 (x0 : nat) (x1 : nat) := @eq real (real_sub (real_of_num x0) (real_of_num x1)).
Definition term18 (x0 : nat) (x1 : nat) := @COND real (Peano.le x1 x0) (real_of_int (int_of_num (Nat.sub x0 x1))).
Definition term23 (x0 : nat) (x1 : nat) := real_of_int (int_neg (int_of_num (Nat.sub x0 x1))).
Definition term5 (x0 : nat) := real_of_int (int_of_num x0).
Definition term15 (x0 : nat) (x1 : nat) := real_of_int (int_of_num (Nat.sub x0 x1)).
Definition term32 (x0 : nat) := forall y0 : nat, (int_sub (int_of_num x0) (int_of_num y0)) = (@COND int (Peano.le y0 x0) (int_of_num (Nat.sub x0 y0)) (int_neg (int_of_num (Nat.sub y0 x0)))).
Definition term1 (x0 : nat) := forall y0 : nat, (real_sub (real_of_num x0) (real_of_num y0)) = (@COND real (Peano.le y0 x0) (real_of_num (Nat.sub x0 y0)) (real_neg (real_of_num (Nat.sub y0 x0)))).
Definition term30 (x0 : nat) (x1 : nat) := int_sub (int_of_num x0) (int_of_num x1).
Definition term31 (x0 : nat) (x1 : nat) := @COND int (Peano.le x0 x1) (int_of_num (Nat.sub x1 x0)) (int_neg (int_of_num (Nat.sub x0 x1))).
Definition term7 (x0 : nat) := real_sub (real_of_int (int_of_num x0)).
Definition term33 := forall y0 : nat, forall y1 : nat, (int_sub (int_of_num y0) (int_of_num y1)) = (@COND int (Peano.le y1 y0) (int_of_num (Nat.sub y0 y1)) (int_neg (int_of_num (Nat.sub y1 y0)))).
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_sub (real_of_num x0) (real_of_num y0)) = (@COND real (Peano.le y0 x0) (real_of_num (Nat.sub x0 y0)) (real_neg (real_of_num (Nat.sub y0 x0))))) x1.
Definition term19 (x0 : nat) (x1 : nat) := real_neg (real_of_num (Nat.sub x0 x1)).
Definition term28 (x0 : nat) (x1 : nat) := real_of_int (@COND int (Peano.le x0 x1) (int_of_num (Nat.sub x1 x0)) (int_neg (int_of_num (Nat.sub x0 x1)))).
Definition term21 (x0 : int) := real_neg (real_of_int x0).
Definition term6 (x0 : nat) := real_sub (real_of_num x0).
Definition term24 (x0 : nat) (x1 : nat) := int_of_num (Nat.sub x0 x1).
Definition term4 (x0 : nat) (x1 : nat) := @COND real (Peano.le x0 x1) (real_of_num (Nat.sub x1 x0)) (real_neg (real_of_num (Nat.sub x0 x1))).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_sub (real_of_num y0) (real_of_num y1)) = (@COND real (Peano.le y1 y0) (real_of_num (Nat.sub y0 y1)) (real_neg (real_of_num (Nat.sub y1 y0))))) x0.
Definition term26 (x0 : Prop) (x1 : int) (x2 : int) := @COND real x0 (real_of_int x1) (real_of_int x2).
Definition term16 (x0 : nat) (x1 : nat) := @COND real (Peano.le x0 x1).
Definition term22 (x0 : int) := real_of_int (int_neg x0).
Definition term8 (x0 : nat) (x1 : nat) := real_sub (real_of_int (int_of_num x0)) (real_of_int (int_of_num x1)).
Definition term11 (x0 : nat) (x1 : nat) := real_of_int (int_sub (int_of_num x0) (int_of_num x1)).
Definition term29 (x0 : nat) (x1 : nat) := int_neg (int_of_num (Nat.sub x0 x1)).
Definition term17 (x0 : nat) (x1 : nat) := @COND real (Peano.le x1 x0) (real_of_num (Nat.sub x0 x1)).
