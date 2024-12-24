Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300430 : forall x : int, forall y : int, (int_abs (int_mul x y)) = (int_mul (int_abs x) (int_abs y)).
