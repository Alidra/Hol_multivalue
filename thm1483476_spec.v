Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483476 : forall (lx : real) (rx : real) (ry : real), (real_mul lx (real_mul rx ry)) = (real_mul (real_mul lx rx) ry).
