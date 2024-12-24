Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem91144 : forall m : nat, forall n : nat, (Peano.le (S m) n) = (Peano.lt m n).
