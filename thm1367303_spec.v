Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1367303 : forall (m : nat), ((real_add (real_neg (real_of_num m)) (real_of_num m)) = (real_of_num (NUMERAL 0))) /\ ((real_add (real_of_num m) (real_neg (real_of_num m))) = (real_of_num (NUMERAL 0))).
