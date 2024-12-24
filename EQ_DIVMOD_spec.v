Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem163266 : forall p : nat, forall m : nat, forall n : nat, (((Nat.div m p) = (Nat.div n p)) /\ ((Nat.modulo m p) = (Nat.modulo n p))) = (m = n).
