Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2304591 : forall x : int, forall y : int, (int_lt (int_neg x) (int_neg y)) = (int_lt y x).
