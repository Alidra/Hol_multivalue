Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2406442 : forall (x : nat), ((int_abs (int_neg (int_of_num x))) = (int_of_num x)) /\ ((int_abs (int_of_num x)) = (int_of_num x)).
