Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1052803 : forall x : nat, forall y : nat, ((NUMFST (NUMPAIR x y)) = x) /\ ((NUMSND (NUMPAIR x y)) = y).
