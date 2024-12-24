Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1535666 : forall x : real, (real_abs (real_abs x)) = (real_abs x).
