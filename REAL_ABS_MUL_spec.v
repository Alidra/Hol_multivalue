Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1582313 : forall x : real, forall y : real, (real_abs (real_mul x y)) = (real_mul (real_abs x) (real_abs y)).
