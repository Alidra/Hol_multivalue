Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1685642 : forall x : real, forall y : real, forall a : real, forall u : real, forall v : real, ((real_le a x) /\ ((real_le a y) /\ ((real_le (real_of_num (NUMERAL 0)) u) /\ ((real_le (real_of_num (NUMERAL 0)) v) /\ ((real_add u v) = (real_of_num (NUMERAL (BIT1 0)))))))) -> real_le a (real_add (real_mul u x) (real_mul v y)).
