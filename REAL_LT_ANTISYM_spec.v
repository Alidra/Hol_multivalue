Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1493879 : forall x : real, forall y : real, ~ ((real_lt x y) /\ (real_lt y x)).
