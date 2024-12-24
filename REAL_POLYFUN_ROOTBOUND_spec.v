Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7537923 : forall n : nat, forall c : nat -> real, (~ (forall i : nat, (@IN nat i (dotdot (NUMERAL 0) n)) -> (c i) = (real_of_num (NUMERAL 0)))) -> (@FINITE real (@GSPEC real (fun GEN_PVAR_345 : real => exists x : real, @SETSPEC real GEN_PVAR_345 ((@sum nat (dotdot (NUMERAL 0) n) (fun i : nat => real_mul (c i) (real_pow x i))) = (real_of_num (NUMERAL 0))) x))) /\ (Peano.le (@CARD real (@GSPEC real (fun GEN_PVAR_346 : real => exists x : real, @SETSPEC real GEN_PVAR_346 ((@sum nat (dotdot (NUMERAL 0) n) (fun i : nat => real_mul (c i) (real_pow x i))) = (real_of_num (NUMERAL 0))) x))) n).
