Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2307518 : forall n : nat, (int_add (int_of_num n) (int_of_num (NUMERAL (BIT1 0)))) = (int_of_num (S n)).
