Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1529646 : forall x : real, forall y : real, real_le (real_abs (real_add x y)) (real_add (real_abs x) (real_abs y)).
