Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416543 : forall (rx : int) (lx : int) (ly : int) (ry : int), (int_mul (int_mul lx ly) (int_mul rx ry)) = (int_mul rx (int_mul (int_mul lx ly) ry)).
