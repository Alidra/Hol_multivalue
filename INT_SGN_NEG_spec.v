Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2309918 : forall x : int, (int_sgn (int_neg x)) = (int_neg (int_sgn x)).
