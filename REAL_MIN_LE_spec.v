Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1568445 : forall x : real, forall y : real, forall z : real, (real_le (real_min x y) z) = ((real_le x z) \/ (real_le y z)).
