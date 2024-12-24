Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1541398 : forall x : real, forall y : real, forall z : real, ((real_lt x z) /\ (real_lt (real_abs (real_sub y x)) (real_sub z x))) -> real_lt y z.
