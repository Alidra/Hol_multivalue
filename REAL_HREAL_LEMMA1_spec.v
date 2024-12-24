Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1346990 : exists r : hreal -> real, (forall x : real, (real_le (real_of_num (NUMERAL 0)) x) = (exists y : hreal, x = (r y))) /\ (forall y : hreal, forall z : hreal, (hreal_le y z) = (real_le (r y) (r z))).
