Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) := real_neg (real_of_num x0).
Definition term0 (x0 : nat) (x1 : nat) := real_add (real_neg (real_of_num (Nat.add x1 x0))) (real_of_num x1).
