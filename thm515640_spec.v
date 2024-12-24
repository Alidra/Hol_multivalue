Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem515640 : forall (n : nat) (m : nat) (p : nat), (fun p' : nat => (Nat.pow m (Nat.add n p')) = (Nat.mul (Nat.pow m n) (Nat.pow m p'))) p.
