Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032084 : forall (rx : nat) (lx : nat), (Nat.mul lx rx) = (Nat.mul rx lx).
