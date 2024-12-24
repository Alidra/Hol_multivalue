Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416551 : forall (lx : int) (rx : int) (ry : int), (int_mul lx (int_mul rx ry)) = (int_mul (int_mul lx rx) ry).
