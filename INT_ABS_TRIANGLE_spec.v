Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300843 : forall x : int, forall y : int, int_le (int_abs (int_add x y)) (int_add (int_abs x) (int_abs y)).
