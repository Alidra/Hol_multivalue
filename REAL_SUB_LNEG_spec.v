Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1519277 : forall x : real, forall y : real, (real_sub (real_neg x) y) = (real_neg (real_add x y)).
