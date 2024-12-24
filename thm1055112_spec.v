Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1055112 : forall x : Prop, forall y : nat, ((NUMLEFT (NUMSUM x y)) = x) /\ ((NUMRIGHT (NUMSUM x y)) = y).
