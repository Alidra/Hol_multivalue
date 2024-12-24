Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1384585 : forall n : nat, real_lt (real_of_num (NUMERAL 0)) (real_of_num (S n)).
