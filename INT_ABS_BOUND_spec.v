Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2300256 : forall x : int, forall y : int, forall d : int, (int_lt (int_abs (int_sub x y)) d) -> int_lt y (int_add x d).
