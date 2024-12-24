Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1361095 : forall x : real, forall y : real, (real_neg (real_add x y)) = (real_add (real_neg x) (real_neg y)).
