Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := int_of_num (num_gcd (@pair nat nat x0 x1)).
Definition term2 (x0 : nat) (x1 : nat) := int_gcd (@pair int int (int_of_num x0) (int_of_num x1)).
Definition term0 (x0 : nat) (x1 : nat) := (fun y0 : nat => (int_of_num (num_gcd (@pair nat nat x0 y0))) = (int_gcd (@pair int int (int_of_num x0) (int_of_num y0)))) x1.
