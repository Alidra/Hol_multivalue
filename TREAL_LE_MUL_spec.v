Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1331691 : forall x : prod hreal hreal, forall y : prod hreal hreal, ((treal_le (treal_of_num (NUMERAL 0)) x) /\ (treal_le (treal_of_num (NUMERAL 0)) y)) -> treal_le (treal_of_num (NUMERAL 0)) (treal_mul x y).
