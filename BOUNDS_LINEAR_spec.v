Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1260452 : forall A : nat, forall B : nat, forall C : nat, (forall n : nat, Peano.le (Nat.mul A n) (Nat.add (Nat.mul B n) C)) = (Peano.le A B).
