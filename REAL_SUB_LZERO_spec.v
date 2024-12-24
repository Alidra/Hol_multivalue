Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1517830 : forall x : real, (real_sub (real_of_num (NUMERAL 0)) x) = (real_neg x).
