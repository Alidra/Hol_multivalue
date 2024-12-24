Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem44145 : forall {A : Type'}, forall P : A -> Prop, (@GABS A P) = (@ε A P).
