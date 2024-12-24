Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1367881 : forall (x : real) (y : real), ((@COND real True x y) = x) /\ ((@COND real False x y) = y).
