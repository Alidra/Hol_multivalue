Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1259397 : forall (d' : nat) (m : nat) (d : nat) (d'' : nat) (h1 : (Nat.add m d') = (Nat.add (Nat.add m d) d'')), Peano.le d (Nat.add d' d'').
