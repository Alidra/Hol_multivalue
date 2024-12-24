Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1032082 : forall (lx : nat) (ly : nat) (rx : nat), (Nat.mul (Nat.mul lx ly) rx) = (Nat.mul lx (Nat.mul ly rx)).
