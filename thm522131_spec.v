Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem522131 : forall (m : nat) (n : nat), (fun n' : nat => (~ (Peano.le m n')) = (Peano.lt n' m)) n.
