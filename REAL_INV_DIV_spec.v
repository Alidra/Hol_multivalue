Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1595376 : forall x : real, forall y : real, (real_inv (real_div x y)) = (real_div y x).
