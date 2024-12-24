Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2800651 : forall a : int, forall b : int, exists d : int, (int_le (int_of_num (NUMERAL 0)) d) /\ ((int_divides d a) /\ ((int_divides d b) /\ (exists x : int, exists y : int, d = (int_add (int_mul a x) (int_mul b y))))).
