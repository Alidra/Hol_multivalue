Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1274816 : forall x : nadd, nadd_eq (nadd_add (nadd_of_num (NUMERAL 0)) x) x.
