Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135078 : (forall m : nat, (Nat.sub m (NUMERAL 0)) = m) /\ (forall m : nat, forall n : nat, (Nat.sub m (S n)) = (Nat.pred (Nat.sub m n))).
