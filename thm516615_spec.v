Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem516615 : forall (m : nat) (n : nat), ((fun n' : nat => (Peano.le m n') = ((m = n') \/ (Peano.lt m n'))) n) = ((Peano.le m n) = ((m = n) \/ (Peano.lt m n))).