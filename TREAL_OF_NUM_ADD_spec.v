Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1327157 : forall m : nat, forall n : nat, treal_eq (treal_add (treal_of_num m) (treal_of_num n)) (treal_of_num (Nat.add m n)).
