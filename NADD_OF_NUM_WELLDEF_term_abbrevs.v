Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) (x1 : nat) := nadd_eq (nadd_of_num x0) (nadd_of_num x1).
Definition term2 (x0 : nat) := (fun y0 : nat => nadd_eq (nadd_of_num y0) (nadd_of_num x0)) x0.
Definition term3 (x0 : nat) := nadd_eq (nadd_of_num x0) (nadd_of_num x0).
Definition term1 (x0 : nat) (x1 : nat) := (fun y0 : nat => nadd_eq (nadd_of_num y0) (nadd_of_num x0)) x1.
Definition term4 (x0 : nat) (x1 : nat) := @eq Prop ((fun y0 : nat => nadd_eq (nadd_of_num y0) (nadd_of_num x0)) x1).
Definition term9 (x0 : nat) := forall y0 : nat, (x0 = y0) -> nadd_eq (nadd_of_num x0) (nadd_of_num y0).
Definition term7 (x0 : nadd) := (fun y0 : nadd => nadd_eq y0 y0) x0.
Definition term8 (x0 : nat) (x1 : nat) := (x0 = x1) -> nadd_eq (nadd_of_num x0) (nadd_of_num x1).
Definition term10 := forall y0 : nat, forall y1 : nat, (y0 = y1) -> nadd_eq (nadd_of_num y0) (nadd_of_num y1).
Definition term0 (x0 : nat) := fun y0 : nat => nadd_eq (nadd_of_num y0) (nadd_of_num x0).
Definition term6 (x0 : nat) (x1 : nat) := @eq Prop (nadd_eq (nadd_of_num x0) (nadd_of_num x1)).
