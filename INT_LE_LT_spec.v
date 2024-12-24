Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302631 : forall x : int, forall y : int, (int_le x y) = ((int_lt x y) \/ (x = y)).
