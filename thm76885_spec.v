Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem76885 : ((Nat.pred (NUMERAL 0)) = (NUMERAL 0)) /\ (forall n : nat, (Nat.pred (S n)) = n).
