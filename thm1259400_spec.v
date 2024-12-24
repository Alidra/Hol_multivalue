Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259400 : forall (p : nat) (d : nat) (d' : nat) (d'' : nat) (h1 : p = (Nat.add (Nat.add (Nat.add p d) d') d'')), Peano.le d (Nat.add d' d'').
