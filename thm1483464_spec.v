Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483464 : forall (lx : real) (rx : real) (ly : real) (ry : real), (real_mul (real_mul lx ly) (real_mul rx ry)) = (real_mul (real_mul lx rx) (real_mul ly ry)).
