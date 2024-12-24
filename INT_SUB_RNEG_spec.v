Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem2310424 : forall x : int, forall y : int, (int_sub x (int_neg y)) = (int_add x y).
