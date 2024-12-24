Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : int) (x1 : nat) := (fun y0 : nat => (real_pow (real_of_int x0) y0) = (real_of_int (int_pow x0 y0))) x1.
Definition term1 (x0 : int) (x1 : nat) := real_pow (real_of_int x0) x1.
Definition term2 (x0 : int) (x1 : nat) := real_of_int (int_pow x0 x1).
