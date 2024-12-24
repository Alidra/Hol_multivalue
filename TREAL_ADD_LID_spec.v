Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1328160 : forall x : prod hreal hreal, treal_eq (treal_add (treal_of_num (NUMERAL 0)) x) x.
