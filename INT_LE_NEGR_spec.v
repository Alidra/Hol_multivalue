Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302998 : forall x : int, (int_le x (int_neg x)) = (int_le x (int_of_num (NUMERAL 0))).
