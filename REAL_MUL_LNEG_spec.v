Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1360913 : forall x : real, forall y : real, (real_mul (real_neg x) y) = (real_neg (real_mul x y)).
