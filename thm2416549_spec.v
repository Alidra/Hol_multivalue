Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2416549 : forall (rx : int) (lx : int), (int_mul lx rx) = (int_mul rx lx).
