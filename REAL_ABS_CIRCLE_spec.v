Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1544390 : forall x : real, forall y : real, forall h : real, (real_lt (real_abs h) (real_sub (real_abs y) (real_abs x))) -> real_lt (real_abs (real_add x h)) (real_abs y).
