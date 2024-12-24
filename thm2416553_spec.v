Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416553 : forall (rx : int) (lx : int) (ry : int), (int_mul lx (int_mul rx ry)) = (int_mul rx (int_mul lx ry)).
