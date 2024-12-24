Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2318243 : forall x : int, forall y : int, (int_ge x y) = (int_le y x).
