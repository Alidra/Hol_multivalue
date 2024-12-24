Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1948489 : forall x : real, (real_abs (sqrt x)) = (sqrt (real_abs x)).
