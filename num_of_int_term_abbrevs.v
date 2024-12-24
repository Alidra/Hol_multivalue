Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term4 (x0 : int) := (fun y0 : int => (num_of_int y0) = (@ε nat (fun y1 : nat => (int_of_num y1) = y0))) x0.
Definition term0 := fun y0 : int => @ε nat (fun y1 : nat => (int_of_num y1) = y0).
Definition term2 (x0 : int) := @ε nat (fun y0 : nat => (int_of_num y0) = x0).
Definition term1 (x0 : int) := (fun y0 : int => @ε nat (fun y1 : nat => (int_of_num y1) = y0)) x0.
Definition term3 := forall y0 : int, (num_of_int y0) = (@ε nat (fun y1 : nat => (int_of_num y1) = y0)).
