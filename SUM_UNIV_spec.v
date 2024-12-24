Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7125050 : forall {A : Type'}, forall f : A -> real, forall s : A -> Prop, (@SUBSET A (@support A real real_add f (@UNIV A)) s) -> (@sum A s f) = (@sum A (@UNIV A) f).
