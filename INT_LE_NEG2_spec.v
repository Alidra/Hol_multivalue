Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2302944 : forall x : int, forall y : int, (int_le (int_neg x) (int_neg y)) = (int_le y x).
