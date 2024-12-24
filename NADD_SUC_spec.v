Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1266568 : forall x : nadd, exists B : nat, forall n : nat, Peano.le (dist (@pair nat nat (dest_nadd x (S n)) (dest_nadd x n))) B.
