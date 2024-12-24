Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := (Peano.lt x1 x0) /\ (Peano.le x0 x1).
Definition term0 (x0 : nat) (x1 : nat) := (~ ((Peano.lt x1 x0) /\ (Peano.le x0 x1))) -> ((Peano.lt x1 x0) /\ (Peano.le x0 x1)) = False.
