Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1247430 : forall (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (Nat.add (Nat.add (Nat.add p d) d') d'')), p = (Nat.add (Nat.add (Nat.add p d) d') d'').
