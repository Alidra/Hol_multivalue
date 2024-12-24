Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1246898 : forall m : nat, forall n : nat, (Peano.le n m) = (~ (Peano.lt m n)).
