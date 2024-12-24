Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem513186 : forall (n : nat), ((fun n' : nat => (Nat.pred (S n')) = n') n) = ((Nat.pred (S n)) = n).
