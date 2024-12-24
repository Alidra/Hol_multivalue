Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416539 : forall (lx : int) (rx : int) (ly : int) (ry : int), (int_mul (int_mul lx ly) (int_mul rx ry)) = (int_mul (int_mul lx rx) (int_mul ly ry)).
