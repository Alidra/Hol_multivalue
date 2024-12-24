Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1267930 : forall x : nadd, forall y : nadd, (nadd_eq x y) = (exists B : nat, forall n : nat, Peano.le (dist (@pair nat nat (dest_nadd x n) (dest_nadd y n))) B).
