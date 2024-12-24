Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1482981 : forall (P : real -> Prop) (x : real), (P (real_abs x)) = (((real_ge x (real_of_num (NUMERAL 0))) /\ (P x)) \/ ((real_gt (real_of_num (NUMERAL 0)) x) /\ (P (real_neg x)))).
