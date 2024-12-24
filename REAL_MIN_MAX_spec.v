Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1555966 : forall x : real, forall y : real, (real_min x y) = (real_neg (real_max (real_neg x) (real_neg y))).
