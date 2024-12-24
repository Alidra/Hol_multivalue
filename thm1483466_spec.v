Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483466 : forall (lx : real) (ly : real) (rx : real) (ry : real), (real_mul (real_mul lx ly) (real_mul rx ry)) = (real_mul lx (real_mul ly (real_mul rx ry))).
