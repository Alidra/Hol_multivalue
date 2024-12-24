Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem3269430 : forall {A : Type'}, forall s : A -> Prop, (@DIFF A s (@UNIV A)) = (@EMPTY A).
