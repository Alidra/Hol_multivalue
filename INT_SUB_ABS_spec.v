Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310099 : forall x : int, forall y : int, int_le (int_sub (int_abs x) (int_abs y)) (int_abs (int_sub x y)).
