Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483448 : forall (a : real), (real_add (real_of_num (NUMERAL 0)) a) = a.