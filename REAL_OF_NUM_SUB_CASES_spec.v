Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1485709 : forall m : nat, forall n : nat, (real_sub (real_of_num m) (real_of_num n)) = (@COND real (Peano.le n m) (real_of_num (Nat.sub m n)) (real_neg (real_of_num (Nat.sub n m)))).
