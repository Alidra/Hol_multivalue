Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841350 : forall m : nat, forall n : nat, (int_of_num (Nat.max m n)) = (int_max (int_of_num m) (int_of_num n)).
