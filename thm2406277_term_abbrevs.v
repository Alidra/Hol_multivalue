Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) := int_add (int_neg (int_of_num (Nat.add x1 x0))) (int_of_num x1).
Definition term1 (x0 : nat) := int_neg (int_of_num x0).
