Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3229314 : forall {A : Type'}, forall s : A -> Prop, (@PSUBSET A s (@UNIV A)) = (exists x : A, ~ (@IN A x s)).
