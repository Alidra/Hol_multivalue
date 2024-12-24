Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841407 : forall (m : nat) (n : nat), (fun n' : nat => (Peano.le m n') = (int_le (int_of_num m) (int_of_num n'))) n.
