Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841383 : forall (m : nat) (n : nat), (fun n' : nat => (int_of_num (Nat.add m n')) = (int_add (int_of_num m) (int_of_num n'))) n.
