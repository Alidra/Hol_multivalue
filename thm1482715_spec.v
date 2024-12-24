Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1482715 : forall (x : real) (a : real) (b : real) (y : real) (c : real) (r : real), ((real_gt (real_add (real_min x y) a) r) = ((real_gt (real_add a x) r) /\ (real_gt (real_add a y) r))) /\ (((real_gt (real_add a (real_min x y)) r) = ((real_gt (real_add a x) r) /\ (real_gt (real_add a y) r))) /\ (((real_gt (real_add a (real_add (real_min x y) b)) r) = ((real_gt (real_add a (real_add x b)) r) /\ (real_gt (real_add a (real_add y b)) r))) /\ (((real_gt (real_add a (real_add b (real_min x y))) r) = ((real_gt (real_add a (real_add b x)) r) /\ (real_gt (real_add a (real_add b y)) r))) /\ ((real_gt (real_add a (real_add b (real_add (real_min x y) c))) r) = ((real_gt (real_add a (real_add b (real_add x c))) r) /\ (real_gt (real_add a (real_add b (real_add y c))) r)))))).
