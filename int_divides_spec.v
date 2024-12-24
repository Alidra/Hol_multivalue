Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2429416 : forall b : int, forall a : int, (int_divides a b) = (exists x : int, b = (int_mul a x)).
