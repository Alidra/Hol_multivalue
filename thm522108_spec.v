Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522108 : forall (m : nat) (n : nat), ((fun n' : nat => (Nat.sub (Nat.add m n') m) = n') n) = ((Nat.sub (Nat.add m n) m) = n).
