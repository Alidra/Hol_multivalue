Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1344936 : forall x : real, forall y : real, (real_div x y) = (real_mul x (real_inv y)).
