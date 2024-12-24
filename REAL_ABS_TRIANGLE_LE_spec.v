Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1530771 : forall x : real, forall y : real, forall z : real, (real_le (real_add (real_abs x) (real_abs (real_sub y x))) z) -> real_le (real_abs y) z.
