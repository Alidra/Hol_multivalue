Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1505819 : forall x : real, (real_le (real_of_num (NUMERAL 0)) (real_add x x)) = (real_le (real_of_num (NUMERAL 0)) x).
