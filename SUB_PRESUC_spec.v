Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135345 : forall m : nat, forall n : nat, (Nat.pred (Nat.sub (S m) n)) = (Nat.sub m n).
