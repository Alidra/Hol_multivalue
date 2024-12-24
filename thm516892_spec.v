Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516892 : forall (m : nat) (n : nat), (fun n' : nat => (Peano.le m (S n')) = ((m = (S n')) \/ (Peano.le m n'))) n.
