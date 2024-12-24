Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1523449 : forall x : real, forall y : real, (real_sub x (real_add x y)) = (real_neg y).
