Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516724 : forall (n : nat), (fun n' : nat => (Nat.add 0 n') = n') n.
