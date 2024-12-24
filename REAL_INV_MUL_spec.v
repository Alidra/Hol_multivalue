Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1595294 : forall x : real, forall y : real, (real_inv (real_mul x y)) = (real_mul (real_inv x) (real_inv y)).
