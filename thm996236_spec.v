Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem996236 : forall (n : nat) (m : nat), ((Nat.mul (BIT1 0) n) = n) /\ ((Nat.mul m (BIT1 0)) = m).