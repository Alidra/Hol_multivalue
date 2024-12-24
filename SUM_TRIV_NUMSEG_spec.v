Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7216202 : forall f : nat -> real, forall m : nat, forall n : nat, (Peano.lt n m) -> (@sum nat (dotdot m n) f) = (real_of_num (NUMERAL 0)).
