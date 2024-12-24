Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1539586 : forall x : real, forall y : real, forall d : real, (real_lt (real_abs (real_sub x y)) d) -> real_lt y (real_add x d).
