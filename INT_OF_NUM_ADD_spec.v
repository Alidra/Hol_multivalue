Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2306816 : forall m : nat, forall n : nat, (int_add (int_of_num m) (int_of_num n)) = (int_of_num (Nat.add m n)).
