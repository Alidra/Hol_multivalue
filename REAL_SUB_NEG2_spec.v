Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1519804 : forall x : real, forall y : real, (real_sub (real_neg x) (real_neg y)) = (real_sub y x).
