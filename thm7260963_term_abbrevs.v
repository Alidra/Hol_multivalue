Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term0 (x0 : nat) (x1 : nat) (x2 : nat -> real) (x3 : nat -> real) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 x1)) -> (x2 y0) = (x3 y0).
