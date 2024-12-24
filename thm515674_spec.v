Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem515674 : forall (n : nat), (fun n' : nat => (Nat.mul 0 n') = 0) n.
