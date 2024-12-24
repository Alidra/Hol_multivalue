Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem150645 : forall x : nat, forall y : nat, forall n : nat, (Peano.le x y) -> Peano.le (Nat.pow x n) (Nat.pow y n).
