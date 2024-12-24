Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2305786 : forall x : int, forall y : int, (int_min x y) = (int_min y x).
