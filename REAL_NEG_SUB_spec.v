Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1374337 : forall x : real, forall y : real, (real_neg (real_sub x y)) = (real_sub y x).
