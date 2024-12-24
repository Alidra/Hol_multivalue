Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338249 : forall (m : nat) (n : nat), (fun n' : nat => (Peano.lt n' m) = (~ (Peano.le m n'))) n.
