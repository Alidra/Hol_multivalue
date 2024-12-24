Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310475 : forall x : int, forall y : int, (int_sub (int_sub x y) x) = (int_neg y).
