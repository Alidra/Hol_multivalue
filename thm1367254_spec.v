Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1367254 : forall (x : nat), ((real_mul (real_of_num x) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))) /\ ((real_mul (real_neg (real_of_num x)) (real_of_num (NUMERAL 0))) = (real_of_num (NUMERAL 0))).
