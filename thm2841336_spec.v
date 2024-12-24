Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2841336 : forall (k : nat), forall n : nat, (int_of_num (Nat.mul (NUMERAL k) n)) = (int_mul (int_of_num (NUMERAL k)) (int_of_num n)).
