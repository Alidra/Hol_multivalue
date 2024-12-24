Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3173052 : forall x : real, forall n : int, (real_zpow x (int_neg n)) = (real_inv (real_zpow x n)).
