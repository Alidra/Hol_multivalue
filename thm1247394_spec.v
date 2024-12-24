Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247394 : forall (d'' : nat) (p : nat) (d : nat) (n : nat) (d' : nat) (h1 : p = (Nat.add n d'')) (h2 : (Nat.add p d) = (Nat.add n d')), (Nat.add (Nat.add n d'') d) = (Nat.add n d').
