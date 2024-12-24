Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1557027 : forall x : real, forall y : real, (real_max x y) = (real_neg (real_min (real_neg x) (real_neg y))).
