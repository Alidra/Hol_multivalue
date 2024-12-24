Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 := (forall y0 : nat, forall y1 : nat, (int_lt (int_of_num y0) (int_of_num y1)) = (Peano.lt y0 y1)) /\ ((forall y0 : nat, forall y1 : nat, (int_max (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.max y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (int_min (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.min y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (int_add (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.add y0 y1))) /\ ((forall y0 : nat, forall y1 : nat, (int_mul (int_of_num y0) (int_of_num y1)) = (int_of_num (Nat.mul y0 y1))) /\ (forall y0 : nat, forall y1 : nat, (int_pow (int_of_num y0) y1) = (int_of_num (Nat.pow y0 y1))))))).
