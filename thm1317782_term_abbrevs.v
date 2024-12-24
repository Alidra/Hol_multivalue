Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := (fun y0 : nat => mk_hreal (fun y1 : nadd => nadd_eq (nadd_of_num y0) y1)) x0.
Definition term5 (x0 : nat) (x1 : nadd) := (nadd_eq (nadd_of_num x0) x1) -> nadd_eq (nadd_of_num x0) x1.
Definition term3 (x0 : nat) := @eq hreal (hreal_of_num x0).
Definition term0 := fun y0 : nat => mk_hreal (fun y1 : nadd => nadd_eq (nadd_of_num y0) y1).
Definition term9 (x0 : nat) := nadd_eq (nadd_of_num x0).
Definition term10 (x0 : nat) := mk_hreal (nadd_eq (nadd_of_num x0)).
Definition term6 (x0 : nat) (x1 : nadd) := ((nadd_eq (nadd_of_num x0) x1) -> nadd_eq (nadd_of_num x0) x1) /\ ((nadd_eq (nadd_of_num x0) x1) -> nadd_eq (nadd_of_num x0) x1).
Definition term8 (x0 : nadd -> Prop) := fun y0 : nadd => x0 y0.
Definition term7 (x0 : nat) := fun y0 : nadd => nadd_eq (nadd_of_num x0) y0.
Definition term4 (x0 : nat) (x1 : nadd) := nadd_eq (nadd_of_num x0) x1.
Definition term2 (x0 : nat) := mk_hreal (fun y0 : nadd => nadd_eq (nadd_of_num x0) y0).
