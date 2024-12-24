Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := real_le (real_of_num x0).
Definition term2 (x0 : nat) (x1 : nat) := real_le (mk_real (treal_eq (treal_of_num x0))) (mk_real (treal_eq (treal_of_num x1))).
Definition term4 (x0 : nat) := real_le (mk_real (treal_eq (treal_of_num x0))).
Definition term12 (x0 : nat) := forall y0 : nat, (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term11 (x0 : nat) := forall y0 : nat, (treal_le (treal_of_num x0) (treal_of_num y0)) = (Peano.le x0 y0).
Definition term10 (x0 : nat) := fun y0 : nat => (real_le (real_of_num x0) (real_of_num y0)) = (Peano.le x0 y0).
Definition term9 (x0 : nat) := fun y0 : nat => (treal_le (treal_of_num x0) (treal_of_num y0)) = (Peano.le x0 y0).
Definition term8 (x0 : nat) (x1 : nat) := @eq Prop (real_le (real_of_num x0) (real_of_num x1)).
Definition term14 := fun y0 : nat => forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1).
Definition term13 := fun y0 : nat => forall y1 : nat, (treal_le (treal_of_num y0) (treal_of_num y1)) = (Peano.le y0 y1).
Definition term16 := forall y0 : nat, forall y1 : nat, (real_le (real_of_num y0) (real_of_num y1)) = (Peano.le y0 y1).
Definition term15 := forall y0 : nat, forall y1 : nat, (treal_le (treal_of_num y0) (treal_of_num y1)) = (Peano.le y0 y1).
Definition term7 (x0 : nat) (x1 : nat) := @eq Prop (treal_le (treal_of_num x0) (treal_of_num x1)).
Definition term0 (x0 : prod hreal hreal) (x1 : prod hreal hreal) := real_le (mk_real (treal_eq x0)) (mk_real (treal_eq x1)).
Definition term3 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term1 (x0 : nat) (x1 : nat) := treal_le (treal_of_num x0) (treal_of_num x1).
Definition term6 (x0 : nat) (x1 : nat) := real_le (real_of_num x0) (real_of_num x1).
