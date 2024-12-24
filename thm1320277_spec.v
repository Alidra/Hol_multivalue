Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1320277 : forall x : hreal, (hreal_add (hreal_of_num (NUMERAL 0)) x) = x.
