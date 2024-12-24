Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7047120 : forall f : nat -> nat, forall n : nat, (@nsum nat (dotdot n n) f) = (f n).
