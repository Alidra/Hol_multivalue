Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1533617 : forall x : real, forall y : real, (real_abs (real_sub x y)) = (real_abs (real_sub y x)).