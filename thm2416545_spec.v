Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416545 : forall (lx : int) (rx : int) (ly : int), (int_mul (int_mul lx ly) rx) = (int_mul (int_mul lx rx) ly).
