Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1694088 : forall x : real, forall y : real, forall a : real, forall b : real, forall u : real, forall v : real, ((real_lt a x) /\ ((real_lt x b) /\ ((real_lt a y) /\ ((real_lt y b) /\ ((real_le (real_of_num (NUMERAL 0)) u) /\ ((real_le (real_of_num (NUMERAL 0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 0)))))))))) -> (real_lt a (real_add (real_mul u x) (real_mul v y))) /\ (real_lt (real_add (real_mul u x) (real_mul v y)) b).