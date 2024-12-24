Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522160 : forall (m : nat) (n : nat), (fun n' : nat => (Nat.sub m (S n')) = (Nat.pred (Nat.sub m n'))) n.
