Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416541 : forall (lx : int) (ly : int) (rx : int) (ry : int), (int_mul (int_mul lx ly) (int_mul rx ry)) = (int_mul lx (int_mul ly (int_mul rx ry))).
