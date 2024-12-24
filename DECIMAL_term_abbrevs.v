Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term6 := forall y0 : nat, forall y1 : nat, (DECIMAL y0 y1) = (real_div (real_of_num y0) (real_of_num y1)).
Definition term0 := fun y0 : nat => fun y1 : nat => real_div (real_of_num y0) (real_of_num y1).
Definition term4 (x0 : nat) (x1 : nat) := real_div (real_of_num x0) (real_of_num x1).
Definition term2 (x0 : nat) := fun y0 : nat => real_div (real_of_num x0) (real_of_num y0).
Definition term8 (x0 : nat) (x1 : nat) := (fun y0 : nat => (DECIMAL x0 y0) = (real_div (real_of_num x0) (real_of_num y0))) x1.
Definition term7 (x0 : nat) := (fun y0 : nat => forall y1 : nat, (DECIMAL y0 y1) = (real_div (real_of_num y0) (real_of_num y1))) x0.
Definition term1 (x0 : nat) := (fun y0 : nat => fun y1 : nat => real_div (real_of_num y0) (real_of_num y1)) x0.
Definition term5 (x0 : nat) := forall y0 : nat, (DECIMAL x0 y0) = (real_div (real_of_num x0) (real_of_num y0)).
Definition term3 (x0 : nat) (x1 : nat) := (fun y0 : nat => real_div (real_of_num x0) (real_of_num y0)) x1.
