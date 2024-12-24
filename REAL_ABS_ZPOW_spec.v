Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3179994 : forall x : real, forall n : int, (real_abs (real_zpow x n)) = (real_zpow (real_abs x) n).
