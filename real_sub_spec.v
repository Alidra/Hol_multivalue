Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1340977 : forall x : real, forall y : real, (real_sub x y) = (real_add x (real_neg y)).
