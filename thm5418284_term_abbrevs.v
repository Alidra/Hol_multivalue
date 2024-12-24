Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_type_abbrevs.
Require Import hol_terms.
Definition term1 (x0 : nat) (x1 : nat) := forall y0 : nat, ((Peano.le x0 y0) /\ (Peano.le y0 (S x1))) = ((y0 = (S x1)) \/ ((Peano.le x0 y0) /\ (Peano.le y0 x1))).
Definition term0 (x0 : nat) (x1 : nat) := Peano.le x0 (S x1).
