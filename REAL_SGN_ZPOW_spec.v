Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3180260 : forall x : real, forall n : int, (real_sgn (real_zpow x n)) = (real_zpow (real_sgn x) n).
