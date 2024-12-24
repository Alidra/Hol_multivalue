Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1484068 : forall n : nat, (real_add (real_of_num n) (real_of_num (NUMERAL (BIT1 0)))) = (real_of_num (S n)).
