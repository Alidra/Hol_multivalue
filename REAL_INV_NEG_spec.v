Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1590208 : forall x : real, (real_inv (real_neg x)) = (real_neg (real_inv x)).
