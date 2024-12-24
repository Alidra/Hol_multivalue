Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3175418 : forall x : real, forall y : real, forall n : int, (real_zpow (real_mul x y) n) = (real_mul (real_zpow x n) (real_zpow y n)).
