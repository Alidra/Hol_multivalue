Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247366 : forall (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : n = (Nat.add p d'')) (h2 : (Nat.add p d) = (Nat.add n d')), (Nat.add p d) = (Nat.add (Nat.add p d'') d').
