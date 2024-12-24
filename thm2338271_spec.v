Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2338271 : forall (m : nat) (n : nat), (fun n' : nat => (int_le (int_of_num m) (int_of_num n')) = (Peano.le m n')) n.
