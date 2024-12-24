Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem178251 : forall m : nat, forall n : nat, forall p : nat, forall q : nat, (m = (Nat.add n (Nat.mul q p))) -> (Nat.modulo m p) = (Nat.modulo n p).
