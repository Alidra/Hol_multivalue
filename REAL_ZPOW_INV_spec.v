Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3174521 : forall x : real, forall n : int, (real_zpow (real_inv x) n) = (real_inv (real_zpow x n)).
