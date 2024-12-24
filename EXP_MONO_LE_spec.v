Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem153228 : forall x : nat, forall y : nat, forall n : nat, (Peano.le (Nat.pow x n) (Nat.pow y n)) = ((Peano.le x y) \/ (n = (NUMERAL 0))).
