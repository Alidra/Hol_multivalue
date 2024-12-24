Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310336 : forall x : int, forall y : int, (int_sub (int_neg x) (int_neg y)) = (int_sub y x).
