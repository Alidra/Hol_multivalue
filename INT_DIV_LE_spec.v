Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2619504 : forall m : int, forall n : int, int_le (int_abs (div m n)) (int_abs m).
