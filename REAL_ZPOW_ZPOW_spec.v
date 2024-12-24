Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3175238 : forall x : real, forall m : int, forall n : int, (real_zpow (real_zpow x m) n) = (real_zpow x (int_mul m n)).
