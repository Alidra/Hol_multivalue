Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3117435 : forall (m : nat) (n : nat), (fun n' : nat => (int_of_num (Nat.mul m n')) = (int_mul (int_of_num m) (int_of_num n'))) n.
