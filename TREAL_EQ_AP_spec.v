Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem1326851 : forall x : prod hreal hreal, forall y : prod hreal hreal, (x = y) -> treal_eq x y.
