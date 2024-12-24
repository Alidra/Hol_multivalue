Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (num_coprime (@pair nat nat x0 y0)) = (int_coprime (@pair int int (int_of_num x0) (int_of_num y0)))) x1.
Definition term1 (x0 : nat) (x1 : nat) := num_coprime (@pair nat nat x0 x1).
Definition term2 (x0 : nat) (x1 : nat) := int_coprime (@pair int int (int_of_num x0) (int_of_num x1)).
