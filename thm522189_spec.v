Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522189 : forall (m : nat) (n : nat), (fun n' : nat => (Nat.sub (S m) (S n')) = (Nat.sub m n')) n.
