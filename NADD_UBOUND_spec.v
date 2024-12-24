Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1299579 : forall x : nadd, exists B : nat, exists N : nat, forall n : nat, (Peano.le N n) -> Peano.le (dest_nadd x n) (Nat.mul B n).
