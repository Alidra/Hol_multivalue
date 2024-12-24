Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2271143 : forall x : int, forall y : int, (int_gt x y) = (real_gt (real_of_int x) (real_of_int y)).
