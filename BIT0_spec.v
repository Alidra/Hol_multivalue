Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem80084 : forall n : nat, (BIT0 n) = (Nat.add n n).