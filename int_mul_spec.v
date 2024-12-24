Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2286307 : forall x : int, forall y : int, (int_mul x y) = (int_of_real (real_mul (real_of_int x) (real_of_int y))).
