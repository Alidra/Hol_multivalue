Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1715400 : forall x : real, (real_sgn (real_neg x)) = (real_neg (real_sgn x)).
