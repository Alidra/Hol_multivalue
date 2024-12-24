Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1734254 : forall x : real, forall y : real, (real_sgn (real_mul x y)) = (real_mul (real_sgn x) (real_sgn y)).
