Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2269769 : forall x : int, forall y : int, (int_lt x y) = (real_lt (real_of_int x) (real_of_int y)).
