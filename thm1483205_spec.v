Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1483205 : forall (y : real) (P : real -> Prop) (x : real), (P (real_max x y)) = (((real_ge y x) /\ (P y)) \/ ((real_gt x y) /\ (P x))).
