Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem317 : forall {A : Type'}, forall x : A, (x = x) = True.