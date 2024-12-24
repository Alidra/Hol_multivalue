Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259399 : forall (n : nat) (d' : nat) (d : nat) (d'' : nat) (h1 : n = (Nat.add (Nat.add (Nat.add n d') d) d'')), Peano.le d (Nat.add d' d'').
