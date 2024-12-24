Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1362291 : forall x : real, forall y : real, (real_le (real_neg x) (real_neg y)) = (real_le y x).
