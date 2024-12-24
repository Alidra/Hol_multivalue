Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522132 : forall (n : nat) (m : nat), ((fun n' : nat => (~ (Peano.le m n')) = (Peano.lt n' m)) n) = ((~ (Peano.le m n)) = (Peano.lt n m)).
