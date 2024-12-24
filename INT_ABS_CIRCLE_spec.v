Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300381 : forall x : int, forall y : int, forall h : int, (int_lt (int_abs h) (int_sub (int_abs y) (int_abs x))) -> int_lt (int_abs (int_add x h)) (int_abs y).
