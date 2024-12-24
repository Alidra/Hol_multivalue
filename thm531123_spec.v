Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem531123 : forall (n : nat), ((fun n' : nat => (Nat.add (BIT1 n') 0) = (BIT1 n')) n) = ((Nat.add (BIT1 n) 0) = (BIT1 n)).
