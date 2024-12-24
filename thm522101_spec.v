Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522101 : forall (m : nat) (n : nat) (p : nat), (fun p' : nat => (Nat.add (Nat.add m n) p') = (Nat.add m (Nat.add n p'))) p.
