Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4211 : forall (q : Prop) (q' : Prop) (p : Prop) (p' : Prop) (h1 : p = p'), (p' -> q = q') -> (p -> q) = (p' -> q').
