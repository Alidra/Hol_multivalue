Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3179019 : forall x : real, forall m : int, forall n : int, (~ (x = (real_of_num (NUMERAL 0)))) -> (real_zpow x (int_add m n)) = (real_mul (real_zpow x m) (real_zpow x n)).
