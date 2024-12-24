Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1947567 : forall x : real, (real_lt (real_of_num (NUMERAL 0)) (sqrt x)) = (real_lt (real_of_num (NUMERAL 0)) x).
