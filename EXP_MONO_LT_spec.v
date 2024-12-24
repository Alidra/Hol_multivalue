Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem153347 : forall x : nat, forall y : nat, forall n : nat, (Peano.lt (Nat.pow x n) (Nat.pow y n)) = ((Peano.lt x y) /\ (~ (n = (NUMERAL 0)))).
