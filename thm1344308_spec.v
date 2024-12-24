Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1344308 : forall x : real, forall n : nat, (real_pow x (S n)) = (real_mul x (real_pow x n)).
