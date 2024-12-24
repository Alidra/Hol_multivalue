Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2531813 : forall a : int, forall n : int, (~ (n = (int_of_num (NUMERAL 0)))) -> exists x : int, (int_le (int_of_num (NUMERAL 0)) x) /\ ((int_lt x (int_abs n)) /\ (@eq2 int x a (int_mod n))).
