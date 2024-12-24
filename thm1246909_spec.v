Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1246909 : forall (m : nat) (n : nat), ((fun n' : nat => (Peano.le n' m) = (~ (Peano.lt m n'))) n) = ((Peano.le n m) = (~ (Peano.lt m n))).
