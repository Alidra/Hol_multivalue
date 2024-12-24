Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300126 : forall x : int, forall y : int, forall z : int, ((int_lt x z) /\ (int_lt (int_abs (int_sub y x)) (int_sub z x))) -> int_lt y z.
