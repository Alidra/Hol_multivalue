Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309505 : forall x : int, forall y : int, ((int_sgn x) = (int_sgn y)) = ((x = y) \/ (int_lt (int_abs (int_sub x y)) (int_max (int_abs x) (int_abs y)))).
