Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516748 : forall (m : nat) (n : nat), (fun n' : nat => (Peano.le (S m) n') = (Peano.lt m n')) n.
