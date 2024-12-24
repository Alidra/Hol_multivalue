Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1641480 : forall x : real, forall m : nat, forall n : nat, (~ (x = (real_of_num (NUMERAL 0)))) -> (real_div (real_pow x m) (real_pow x n)) = (@COND real (Peano.le n m) (real_pow x (Nat.sub m n)) (real_inv (real_pow x (Nat.sub n m)))).
