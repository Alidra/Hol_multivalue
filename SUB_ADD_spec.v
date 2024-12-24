Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem136494 : forall m : nat, forall n : nat, (Peano.le n m) -> (Nat.add (Nat.sub m n) n) = m.
