Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term8 (x0 : nat) := real_abs (real_of_num x0).
Definition term14 (x0 : nat) := real_neg (real_of_num x0).
Definition term22 (a0 : Type') (x0 : Prop) := forall y0 : a0, x0.
Definition term3 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term0 (x0 : nat) := (fun y0 : nat => Peano.le (NUMERAL 0) y0) x0.
Definition term13 (x0 : nat) := @COND real True (real_of_num x0).
Definition term17 (x0 : nat) := @eq real (real_of_num x0).
Definition term11 (x0 : nat) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)).
Definition term18 := fun y0 : nat => (real_abs (real_of_num y0)) = (real_of_num y0).
Definition term10 (x0 : nat) := real_le (real_of_num (NUMERAL 0)) (real_of_num x0).
Definition term4 (x0 : nat) (x1 : nat) := (fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0)) x1.
Definition term21 := forall y0 : nat, True.
Definition term1 (x0 : nat) := Peano.le (NUMERAL 0) x0.
Definition term19 := fun y0 : nat => True.
Definition term6 (x0 : real) := (fun y0 : real => (real_abs y0) = (@COND real (real_le (real_of_num (NUMERAL 0)) y0) y0 (real_neg y0))) x0.
Definition term12 (x0 : nat) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)) (real_of_num x0).
Definition term7 (x0 : real) := @COND real (real_le (real_of_num (NUMERAL 0)) x0) x0 (real_neg x0).
Definition term2 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1)) x0.
Definition term15 (x0 : nat) := @COND real True (real_of_num x0) (real_neg (real_of_num x0)).
Definition term20 := forall y0 : nat, (real_abs (real_of_num y0)) = (real_of_num y0).
Definition term9 (x0 : nat) := @COND real (real_le (real_of_num (NUMERAL 0)) (real_of_num x0)) (real_of_num x0) (real_neg (real_of_num x0)).
Definition term23 (x0 : Prop) := forall y0 : nat, x0.
Definition term5 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
Definition term16 (x0 : nat) := @eq real (real_abs (real_of_num x0)).
