Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1347548 : exists h : real -> hreal, exists r : hreal -> real, (forall x : hreal, (h (r x)) = x) /\ ((forall x : real, (real_le (real_of_num (NUMERAL 0)) x) -> (r (h x)) = x) /\ ((forall x : hreal, real_le (real_of_num (NUMERAL 0)) (r x)) /\ (forall x : hreal, forall y : hreal, (hreal_le x y) = (real_le (r x) (r y))))).
