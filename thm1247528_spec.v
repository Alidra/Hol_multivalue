Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247528 : forall (d' : nat) (d : nat) (n : nat) (d'' : nat) (h1 : (Nat.add (Nat.add n d') d) = (Nat.add n d'')), (Nat.add (Nat.add n d') d) = (Nat.add n d'').
