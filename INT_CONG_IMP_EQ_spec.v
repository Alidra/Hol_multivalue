Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2443203 : forall x : int, forall y : int, forall n : int, ((int_lt (int_abs (int_sub x y)) n) /\ (@eq2 int x y (int_mod n))) -> x = y.
