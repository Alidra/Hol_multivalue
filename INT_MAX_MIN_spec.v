Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305415 : forall x : int, forall y : int, (int_max x y) = (int_neg (int_min (int_neg x) (int_neg y))).
