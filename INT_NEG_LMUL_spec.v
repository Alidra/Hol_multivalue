Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306550 : forall x : int, forall y : int, (int_neg (int_mul x y)) = (int_mul (int_neg x) y).
