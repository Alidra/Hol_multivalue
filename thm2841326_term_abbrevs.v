Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term9 := forall y0 : nat, forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1)).
Definition term8 := forall y0 : nat, forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1)).
Definition term5 (x0 : nat) := forall y0 : nat, (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0)).
Definition term4 (x0 : nat) := forall y0 : nat, (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0)).
Definition term2 (x0 : nat) := fun y0 : nat => (int_add (int_of_num x0) (int_of_num y0)) = (int_of_num (Nat.add x0 y0)).
Definition term3 (x0 : nat) := fun y0 : nat => (int_of_num (Nat.add x0 y0)) = (int_add (int_of_num x0) (int_of_num y0)).
Definition term6 := fun y0 : nat => forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1)).
Definition term1 (x0 : nat) (x1 : nat) := int_of_num (Nat.add x0 x1).
Definition term0 (x0 : nat) (x1 : nat) := int_add (int_of_num x0) (int_of_num x1).
Definition term7 := fun y0 : nat => forall y1 : nat, (int_of_num (Nat.add y0 y1)) = (int_add (int_of_num y0) (int_of_num y1)).