Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305733 : forall x : int, forall y : int, (int_min x y) = (int_neg (int_max (int_neg x) (int_neg y))).