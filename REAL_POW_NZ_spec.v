Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1598144 : forall x : real, forall n : nat, (~ (x = (real_of_num (NUMERAL 0)))) -> ~ ((real_pow x n) = (real_of_num (NUMERAL 0))).
