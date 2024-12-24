Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307278 : forall m : nat, forall n : nat, (int_max (int_of_num m) (int_of_num n)) = (int_of_num (Nat.max m n)).
