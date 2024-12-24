Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term5 (x0 : nat) := @eq real (real_of_int (int_of_num x0)).
Definition term8 (x0 : nat) := forall y0 : nat, ((int_of_num x0) = (int_of_num y0)) = (x0 = y0).
Definition term1 (x0 : nat) := forall y0 : nat, ((real_of_num x0) = (real_of_num y0)) = (x0 = y0).
Definition term4 (x0 : nat) := @eq real (real_of_num x0).
Definition term3 (x0 : nat) := real_of_int (int_of_num x0).
Definition term9 := forall y0 : nat, forall y1 : nat, ((int_of_num y0) = (int_of_num y1)) = (y0 = y1).
Definition term6 (x0 : nat) (x1 : nat) := @eq Prop ((real_of_num x0) = (real_of_num x1)).
Definition term7 (x0 : nat) (x1 : nat) := @eq Prop ((int_of_num x0) = (int_of_num x1)).
Definition term0 (x0 : nat) := (fun y0 : nat => forall y1 : nat, ((real_of_num y0) = (real_of_num y1)) = (y0 = y1)) x0.
Definition term2 (x0 : nat) (x1 : nat) := (fun y0 : nat => ((real_of_num x0) = (real_of_num y0)) = (x0 = y0)) x1.
