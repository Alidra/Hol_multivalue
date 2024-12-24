Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1488302 : forall x : real, forall y : real, ((real_add x y) = x) = (y = (real_of_num (NUMERAL 0))).
