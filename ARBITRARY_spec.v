Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem4853019 : forall {A : Type'}, forall s : (A -> Prop) -> Prop, (@ARBITRARY A s) = True.
