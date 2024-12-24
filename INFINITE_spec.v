Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3198543 : forall {A : Type'}, forall s : A -> Prop, (@INFINITE A s) = (~ (@FINITE A s)).
