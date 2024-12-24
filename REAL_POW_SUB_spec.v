Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1598415 : forall x : real, forall m : nat, forall n : nat, ((~ (x = (real_of_num (NUMERAL 0)))) /\ (Peano.le m n)) -> (real_pow x (Nat.sub n m)) = (real_div (real_pow x n) (real_pow x m)).
