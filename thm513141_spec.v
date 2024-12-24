Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513141 : ((Nat.pred 0) = 0) /\ (forall n : nat, (Nat.pred (S n)) = n).
