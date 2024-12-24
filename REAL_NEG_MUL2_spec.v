Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1491878 : forall x : real, forall y : real, (real_mul (real_neg x) (real_neg y)) = (real_mul x y).
