Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem102387 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, ((Peano.le m n) /\ (Peano.le p q)) -> Peano.le (Nat.mul m p) (Nat.mul n q).
