Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982751 : forall (rx : real) (lx : real) (ry : real), (real_mul lx (real_mul rx ry)) = (real_mul rx (real_mul lx ry)).
