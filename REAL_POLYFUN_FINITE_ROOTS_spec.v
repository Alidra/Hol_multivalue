Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7539125 : forall n : nat, forall c : nat -> real, (@FINITE real (@GSPEC real (fun GEN_PVAR_348 : real => exists x : real, @SETSPEC real GEN_PVAR_348 ((@sum nat (dotdot (NUMERAL 0) n) (fun i : nat => real_mul (c i) (real_pow x i))) = (real_of_num (NUMERAL 0))) x))) = (exists i : nat, (@IN nat i (dotdot (NUMERAL 0) n)) /\ (~ ((c i) = (real_of_num (NUMERAL 0))))).
