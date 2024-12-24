Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3174478 : forall x : real, forall n : int, (real_inv (real_zpow x n)) = (real_zpow (real_inv x) n).
