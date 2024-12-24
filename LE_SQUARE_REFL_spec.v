Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem106282 : forall n : nat, Peano.le n (Nat.mul n n).
