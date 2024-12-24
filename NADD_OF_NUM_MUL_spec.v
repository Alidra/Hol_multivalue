Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1279539 : forall m : nat, forall n : nat, nadd_eq (nadd_mul (nadd_of_num m) (nadd_of_num n)) (nadd_of_num (Nat.mul m n)).
