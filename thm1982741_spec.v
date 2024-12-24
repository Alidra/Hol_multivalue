Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982741 : forall (rx : real) (lx : real) (ly : real) (ry : real), (real_mul (real_mul lx ly) (real_mul rx ry)) = (real_mul rx (real_mul (real_mul lx ly) ry)).
