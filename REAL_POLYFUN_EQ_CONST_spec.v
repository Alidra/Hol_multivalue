Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7552219 : forall n : nat, forall c : nat -> real, forall k : real, (forall x : real, (@sum nat (dotdot (NUMERAL 0) n) (fun i : nat => real_mul (c i) (real_pow x i))) = k) = (((c (NUMERAL 0)) = k) /\ (forall i : nat, (@IN nat i (dotdot (NUMERAL (BIT1 0)) n)) -> (c i) = (real_of_num (NUMERAL 0)))).
