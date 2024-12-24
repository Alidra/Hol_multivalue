Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1495214 : forall x : real, forall y : real, (~ (x = y)) = ((real_lt x y) \/ (real_lt y x)).
