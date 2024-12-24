Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1545462 : forall x : real, forall y : real, real_le (real_sub (real_abs x) (real_abs y)) (real_abs (real_sub x y)).
