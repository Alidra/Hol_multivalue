Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1982743 : forall (lx : real) (rx : real) (ly : real), (real_mul (real_mul lx ly) rx) = (real_mul (real_mul lx rx) ly).
