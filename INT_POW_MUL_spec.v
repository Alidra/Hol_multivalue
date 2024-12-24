Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2308770 : forall x : int, forall y : int, forall n : nat, (int_pow (int_mul x y) n) = (int_mul (int_pow x n) (int_pow y n)).
