Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305436 : forall x : int, forall y : int, (int_max x y) = (int_max y x).
