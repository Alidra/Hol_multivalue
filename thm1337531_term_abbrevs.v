Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 (x0 : nat) := treal_eq (treal_of_num x0).
Definition term1 (x0 : nat) := (fun y0 : nat => mk_real (fun y1 : prod hreal hreal => treal_eq (treal_of_num y0) y1)) x0.
Definition term5 (x0 : nat) (x1 : prod hreal hreal) := (treal_eq (treal_of_num x0) x1) -> treal_eq (treal_of_num x0) x1.
Definition term3 (x0 : nat) := @eq real (real_of_num x0).
Definition term0 := fun y0 : nat => mk_real (fun y1 : prod hreal hreal => treal_eq (treal_of_num y0) y1).
Definition term10 (x0 : nat) := mk_real (treal_eq (treal_of_num x0)).
Definition term6 (x0 : nat) (x1 : prod hreal hreal) := ((treal_eq (treal_of_num x0) x1) -> treal_eq (treal_of_num x0) x1) /\ ((treal_eq (treal_of_num x0) x1) -> treal_eq (treal_of_num x0) x1).
Definition term4 (x0 : nat) (x1 : prod hreal hreal) := treal_eq (treal_of_num x0) x1.
Definition term2 (x0 : nat) := mk_real (fun y0 : prod hreal hreal => treal_eq (treal_of_num x0) y0).
Definition term7 (x0 : nat) := fun y0 : prod hreal hreal => treal_eq (treal_of_num x0) y0.
Definition term8 (x0 : type1233) := fun y0 : prod hreal hreal => x0 y0.
