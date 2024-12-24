Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841401 : forall (m : nat) (n : nat), (fun n' : nat => (Peano.lt m n') = (int_lt (int_of_num m) (int_of_num n'))) n.
