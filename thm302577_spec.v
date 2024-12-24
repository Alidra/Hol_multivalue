Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem302577 : forall (m : nat) (n : nat) (p : nat), (fun p' : nat => ((Nat.add m p') = (Nat.add n p')) = (m = n)) p.
