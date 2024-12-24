Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1367770 : forall (m : nat) (n : nat), (real_add (real_of_num m) (real_of_num n)) = (real_of_num (Nat.add m n)).
