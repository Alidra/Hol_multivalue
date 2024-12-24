Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2385714 : forall m : int, forall n : int, exists q : int, exists r : int, @COND Prop (n = (int_of_num (NUMERAL 0))) ((q = (int_of_num (NUMERAL 0))) /\ (r = m)) ((int_le (int_of_num (NUMERAL 0)) r) /\ ((int_lt r (int_abs n)) /\ (m = (int_add (int_mul q n) r)))).
