Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1821194 : forall x : real, forall y : real, ((real_sgn x) = (real_sgn y)) = ((x = y) \/ (real_lt (real_abs (real_sub x y)) (real_max (real_abs x) (real_abs y)))).
