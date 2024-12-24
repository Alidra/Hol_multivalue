Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483472 : forall (lx : real) (ly : real) (rx : real), (real_mul (real_mul lx ly) rx) = (real_mul lx (real_mul ly rx)).
