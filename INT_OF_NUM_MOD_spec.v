Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307350 : forall m : nat, forall n : nat, (int_of_num (Nat.modulo m n)) = (int_sub (int_of_num m) (int_mul (int_of_num (Nat.div m n)) (int_of_num n))).
