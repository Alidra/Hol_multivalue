Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := fun y0 : int => fun y1 : nat => int_of_real (real_pow (real_of_int y0) y1).
Definition term7 (x0 : int) := (fun y0 : int => forall y1 : nat, (int_pow y0 y1) = (int_of_real (real_pow (real_of_int y0) y1))) x0.
Definition term3 (x0 : int) (x1 : nat) := (fun y0 : nat => int_of_real (real_pow (real_of_int x0) y0)) x1.
Definition term6 := forall y0 : int, forall y1 : nat, (int_pow y0 y1) = (int_of_real (real_pow (real_of_int y0) y1)).
Definition term2 (x0 : int) := fun y0 : nat => int_of_real (real_pow (real_of_int x0) y0).
Definition term1 (x0 : int) := (fun y0 : int => fun y1 : nat => int_of_real (real_pow (real_of_int y0) y1)) x0.
Definition term8 (x0 : int) (x1 : nat) := (fun y0 : nat => (int_pow x0 y0) = (int_of_real (real_pow (real_of_int x0) y0))) x1.
Definition term5 (x0 : int) := forall y0 : nat, (int_pow x0 y0) = (int_of_real (real_pow (real_of_int x0) y0)).
Definition term4 (x0 : int) (x1 : nat) := int_of_real (real_pow (real_of_int x0) x1).
