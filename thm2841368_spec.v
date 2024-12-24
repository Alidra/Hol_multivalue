Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841368 : forall (m : nat) (n : nat), (fun n' : nat => (int_of_num (Nat.min m n')) = (int_min (int_of_num m) (int_of_num n'))) n.
