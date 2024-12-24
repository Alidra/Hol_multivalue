Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem135645 : forall m : nat, forall n : nat, (Nat.sub (S m) (S n)) = (Nat.sub m n).
