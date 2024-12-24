Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term12 (x0 : nat) := forall y0 : nat, (hreal_le (hreal_of_num x0) (hreal_of_num y0)) = (Peano.le x0 y0).
Definition term11 (x0 : nat) := forall y0 : nat, (nadd_le (nadd_of_num x0) (nadd_of_num y0)) = (Peano.le x0 y0).
Definition term10 (x0 : nat) := fun y0 : nat => (hreal_le (hreal_of_num x0) (hreal_of_num y0)) = (Peano.le x0 y0).
Definition term9 (x0 : nat) := fun y0 : nat => (nadd_le (nadd_of_num x0) (nadd_of_num y0)) = (Peano.le x0 y0).
Definition term14 := fun y0 : nat => forall y1 : nat, (hreal_le (hreal_of_num y0) (hreal_of_num y1)) = (Peano.le y0 y1).
Definition term13 := fun y0 : nat => forall y1 : nat, (nadd_le (nadd_of_num y0) (nadd_of_num y1)) = (Peano.le y0 y1).
Definition term3 (x0 : nat) := mk_hreal (nadd_eq (nadd_of_num x0)).
Definition term0 (x0 : nadd) (x1 : nadd) := hreal_le (mk_hreal (nadd_eq x0)) (mk_hreal (nadd_eq x1)).
Definition term6 (x0 : nat) (x1 : nat) := hreal_le (hreal_of_num x0) (hreal_of_num x1).
Definition term16 := forall y0 : nat, forall y1 : nat, (hreal_le (hreal_of_num y0) (hreal_of_num y1)) = (Peano.le y0 y1).
Definition term15 := forall y0 : nat, forall y1 : nat, (nadd_le (nadd_of_num y0) (nadd_of_num y1)) = (Peano.le y0 y1).
Definition term5 (x0 : nat) := hreal_le (hreal_of_num x0).
Definition term7 (x0 : nat) (x1 : nat) := @eq Prop (nadd_le (nadd_of_num x0) (nadd_of_num x1)).
Definition term4 (x0 : nat) := hreal_le (mk_hreal (nadd_eq (nadd_of_num x0))).
Definition term8 (x0 : nat) (x1 : nat) := @eq Prop (hreal_le (hreal_of_num x0) (hreal_of_num x1)).
Definition term1 (x0 : nat) (x1 : nat) := nadd_le (nadd_of_num x0) (nadd_of_num x1).
Definition term2 (x0 : nat) (x1 : nat) := hreal_le (mk_hreal (nadd_eq (nadd_of_num x0))) (mk_hreal (nadd_eq (nadd_of_num x1))).
