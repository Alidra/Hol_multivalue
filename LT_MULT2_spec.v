Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem106179 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((Peano.lt m n) /\ (Peano.lt p q)) -> Peano.lt (Nat.mul m p) (Nat.mul n q).
