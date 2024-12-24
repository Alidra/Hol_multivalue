Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1321694 : forall n : hreal, (hreal_add n (hreal_of_num (NUMERAL 0))) = n.
