Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem996664 : forall (m : nat) (n : nat) (p : nat), ((Nat.mul m n) = p) = ((Nat.mul (BIT0 m) n) = (BIT0 p)).
