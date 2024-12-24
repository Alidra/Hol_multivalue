Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2541191 : forall n : int, (rem n n) = (int_of_num (NUMERAL 0)).
