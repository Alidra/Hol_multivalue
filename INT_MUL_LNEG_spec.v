Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306015 : forall x : int, forall y : int, (int_mul (int_neg x) y) = (int_neg (int_mul x y)).
