Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1999796 : forall (x : real) (y : real), ((real_lt x y) = ((real_lt x y) /\ (~ (x = y)))) = ((real_lt x y) = ((real_lt x y) /\ (~ (x = y)))).
