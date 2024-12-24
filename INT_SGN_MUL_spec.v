Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309890 : forall x : int, forall y : int, (int_sgn (int_mul x y)) = (int_mul (int_sgn x) (int_sgn y)).
