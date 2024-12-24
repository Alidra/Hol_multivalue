Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1595570 : forall x : real, forall y : real, forall n : nat, (real_pow (real_mul x y) n) = (real_mul (real_pow x n) (real_pow y n)).
