Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302578 : forall (p : nat) (m : nat) (n : nat), ((fun p' : nat => ((Nat.add m p') = (Nat.add n p')) = (m = n)) p) = (((Nat.add m p) = (Nat.add n p)) = (m = n)).
