Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1669963 : forall m : nat, forall n : nat, (real_of_num (Nat.modulo m n)) = (real_sub (real_of_num m) (real_mul (real_of_num (Nat.div m n)) (real_of_num n))).
