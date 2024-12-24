Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7221565 : forall f : nat -> real, forall n : nat, (@sum nat (dotdot n n) f) = (f n).
