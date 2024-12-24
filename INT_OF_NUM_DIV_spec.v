Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2538105 : forall m : nat, forall n : nat, (div (int_of_num m) (int_of_num n)) = (int_of_num (Nat.div m n)).
