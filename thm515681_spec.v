Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem515681 : forall (m : nat) (n : nat), (fun n' : nat => (Nat.pow m (S n')) = (Nat.mul m (Nat.pow m n'))) n.
