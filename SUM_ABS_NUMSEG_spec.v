Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7213740 : forall f : nat -> real, forall m : nat, forall n : nat, real_le (real_abs (@sum nat (dotdot m n) f)) (@sum nat (dotdot m n) (fun i : nat => real_abs (f i))).
