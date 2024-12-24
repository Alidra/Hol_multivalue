Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1594832 : forall x : real, (real_abs (real_inv x)) = (real_inv (real_abs x)).
