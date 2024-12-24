Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2406281 : forall (m : nat) (n : nat), (int_add (int_of_num m) (int_neg (int_of_num (Nat.add m n)))) = (int_neg (int_of_num n)).
