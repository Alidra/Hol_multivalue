Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1510621 : forall x : real, forall y : real, (real_le y (real_add x y)) = (real_le (real_of_num (NUMERAL 0)) x).
