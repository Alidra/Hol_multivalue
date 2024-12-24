Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483429 : forall (x : real) (P : real -> Prop) (y : real), (P (real_min x y)) = (((real_ge y x) /\ (P x)) \/ ((real_gt x y) /\ (P y))).
