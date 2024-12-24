Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem531066 : forall (n : nat), (Nat.add (BIT0 n) 0) = (BIT0 n).
