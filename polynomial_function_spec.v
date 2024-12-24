Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7553488 : forall p : real -> real, (polynomial_function p) = (exists m : nat, exists c : nat -> real, forall x : real, (p x) = (@sum nat (dotdot (NUMERAL 0) m) (fun i : nat => real_mul (c i) (real_pow x i)))).
