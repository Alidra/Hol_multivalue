Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032098 : forall (c : nat) (a : nat), (Nat.add a c) = (Nat.add c a).
