Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302664 : forall x : int, forall y : int, forall z : int, (int_le z (int_max x y)) = ((int_le z x) \/ (int_le z y)).
