Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1267115 : forall x : nadd, exists B : nat, forall m : nat, forall n : nat, Peano.le (dist (@pair nat nat (dest_nadd x m) (dest_nadd x n))) (Nat.mul B (dist (@pair nat nat m n))).
