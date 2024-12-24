Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem151921 : forall x : nat, forall y : nat, forall n : nat, ((Peano.lt x y) /\ (~ (n = (NUMERAL 0)))) -> Peano.lt (Nat.pow x n) (Nat.pow y n).
