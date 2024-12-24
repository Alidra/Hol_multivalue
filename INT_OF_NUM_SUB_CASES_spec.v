Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307491 : forall m : nat, forall n : nat, (int_sub (int_of_num m) (int_of_num n)) = (@COND int (Peano.le n m) (int_of_num (Nat.sub m n)) (int_neg (int_of_num (Nat.sub n m)))).
