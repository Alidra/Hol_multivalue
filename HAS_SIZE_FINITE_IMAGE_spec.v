Require Import coq.
Require Import theory_hol.
Require Import hol_types.
Require Import hol_terms.
Axiom lem7605765 : forall {A : Type'}, forall s : A -> Prop, @HAS_SIZE (finite_image A) (@UNIV (finite_image A)) (@dimindex A s).
